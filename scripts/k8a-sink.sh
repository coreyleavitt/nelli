#!/usr/bin/env bash
# RFC-0016 K8a-sink (§10): the triage sink behind .github/workflows/k8a-differential.yaml.
# Turns the nightly's findings into `rfc-0016-intake` issues, one per KEY.
#
#   k8a-sink.sh file --findings FILE --row ROW [--threeway TSV] [--existing TSV]
#                    [--run-url URL] [--no-reduce] [--max-rounds N] [--dry-run]
#   k8a-sink.sh pair                 stdin: one finding; stdout: its verdict pair
#   k8a-sink.sh --self-test
#
# INPUT. findings.txt as k8a-nightly.sh writes it: `FINDING seed=S prog=P
# variant=V shape=Sh` blocks (an empty file = nothing to file, exit 0 and no
# `gh` call at all), the three-way TSV for the table columns, the build row.
#
# KEY (the dedup key; tests/s0016_k8a_sink.nim `dedupKey` is its twin):
#   <cell>|<row>|<verdict pair>
# cell = the universe cell of the program's shape (`construct:k8a-gen/<Shape>`),
# row = the build row, pair = `<walker verdict>|<native outcome>` or
# `meta:<original>|<twin>`. Many seeds and programs hitting one cell the same
# way on one row are ONE issue. The key rides in the issue body as an HTML
# comment, `<!-- k8a-sink-key: KEY -->`, which is what dedup reads.
#
# FILING. Per key, in finding order: no open `rfc-0016-intake` issue carries the
# marker -> `gh issue create` (the first finding of the key is REDUCED first,
# unless --no-reduce: tests/s0016_k8a_reduce.nim, one compile per round, up to
# --max-rounds, see tests/s0016_k8a_sink.nim); one does -> `gh issue comment`
# on it (no reduction, the seed and repro only). Several findings of one key in
# one run are listed together in a single filing. The label already exists;
# this script never creates labels. Open issues are read with a read-only
# `gh issue list`; --existing FILE (lines `number<TAB>key`) replaces that read,
# and with --dry-run the keys it would file are appended to it, so a second
# dry run sees them as open.
#
# --dry-run prints the `gh` commands (and the bodies) and runs no `gh` at all.
set -uo pipefail
cd "$(dirname "$0")/.."

LABEL=rfc-0016-intake
die() { echo "k8a-sink: $*" >&2; exit 2; }

# pair: stdin = a finding; the shell twin of s0016_k8a_sink.nim `verdictPair`.
pair() {
  local f st; f="$(cat)"
  case "$f" in
    *"metamorphic: original "*)
      local rest o t
      rest="${f#*metamorphic: original }"
      o="${rest%% vs twin *}"
      t="${rest#* vs twin }"; t="${t%%$'\n'*}"
      echo "meta:$o|$t"; return ;;
    *"walker says "*)
      st="${f#*walker says }"; st="${st%%[ (]*}"
      case "$f" in
        *"does not hit natively"*) echo "$st|native-miss" ;;
        *"hits it natively"*) echo "$st|native-hit" ;;
        *) echo "$st|native-mismatch" ;;
      esac; return ;;
    *annotationViolations*) echo "annotation|-"; return ;;
  esac
  echo "other|-"
}

# split_findings <file> <dir>: block files <dir>/b<N>.txt, N from 1.
split_findings() {
  awk -v d="$2" '
    /^FINDING /{ n++; f = d "/b" n ".txt"; sub(/^FINDING /, ""); print > f; next }
    n { print > f }' "$1"
}

field() { # field <name> <header line>
  local v; v="$(printf '%s\n' "$2" | tr ' ' '\n' | sed -n "s/^$1=//p" | head -1)"
  printf '%s' "$v"
}

reduce_block() { # reduce_block <seed> <prog> <variant> <outprefix> <backend> <image> <rounds>
  local seed="$1" prog="$2" variant="$3" out="$4" backend="$5" image="$6" rounds="$7"
  local case_enc="" r flags log changed
  local -a ia=()
  [ -n "$image" ] && [ "$image" != latest ] && [ -z "${NELLI_HOST:-}" ] && ia=(-i "$image")
  : > "$out.pair"; : > "$out.src"
  for (( r = 1; r <= rounds; r++ )); do
    if [ -z "$case_enc" ]; then
      flags="-d:k8aSeed=$seed -d:k8aProgId=$prog -d:k8aVariant=$variant"
    else
      flags="-d:k8aSeed=$seed -d:k8aStart=$case_enc"
    fi
    log="$out.round$r.log"
    NELLI_NIM_FLAGS="${NELLI_NIM_FLAGS:-} $flags" \
      scripts/dt-bounded.sh ${ia[@]+"${ia[@]}"} "$backend" tests/s0016_k8a_reduce.nim 900 > "$log" 2>&1 || {
        echo "k8a-sink: reduction round $r failed (rc=$?); using what we have" >&2; break; }
    changed="$(sed -n 's/^K8ARED-CHANGED //p' "$log" | head -1)"
    case_enc="$(sed -n 's/^K8ARED-CASE //p' "$log" | head -1)"
    sed -n '/^K8ARED-SRC-BEGIN/,/^K8ARED-SRC-END/p' "$log" | sed '1d;$d' > "$out.src"
    local pr; pr="$(sed -n 's/^K8ARED-PAIR //p' "$log" | head -1)"
    [ -z "$pr" ] || printf '%s' "$pr" > "$out.pair"
    [ "$changed" = 1 ] || break
  done
}

threeway_rows() { # threeway_rows <tsv> <seed> <prog>
  [ -n "$1" ] && [ -f "$1" ] || { echo "(no three-way table)"; return; }
  { head -1 "$1"; awk -F'\t' -v s="$2" -v p="prog$3 " '$1 == s && index($2, p) == 1' "$1"; } \
    | awk 'NR == 1 || NF' | sed 's/\t/  |  /g'
}

repro_cmd() { # repro_cmd <row> <seed> <prog>
  local backend image
  eval "$(bash scripts/k8a-nightly.sh plan --row "$1" --seed "$2" | grep -E '^(backend|image)=')"
  local img=""
  [ "$image" = latest ] || img="-i $image "
  echo "NELLI_NIM_FLAGS=\"-d:k8aSeed=$2 -d:k8aCount=1 -d:k8aFirst=$3\" scripts/dt-bounded.sh ${img}${backend} tests/tsymex_0016_k8a_gen.nim 900"
}

file_cmd() {
  local findings="" row="" tw="" existing="" runurl="" reduce=1 rounds=6 dry=0
  while [ $# -gt 0 ]; do
    case "$1" in
      --findings) findings="$2"; shift 2 ;;
      --row) row="$2"; shift 2 ;;
      --threeway) tw="$2"; shift 2 ;;
      --existing) existing="$2"; shift 2 ;;
      --run-url) runurl="$2"; shift 2 ;;
      --no-reduce) reduce=0; shift ;;
      --max-rounds) rounds="$2"; shift 2 ;;
      --dry-run) dry=1; shift ;;
      *) die "file: unknown argument $1" ;;
    esac
  done
  [ -n "$findings" ] && [ -n "$row" ] || die "usage: file --findings FILE --row ROW [options]"
  [ -f "$findings" ] || { echo "k8a-sink: no findings file '$findings'; nothing to file"; return 0; }
  local backend image
  eval "$(bash scripts/k8a-nightly.sh plan --row "$row" | grep -E '^(backend|image)=')" || die "bad row '$row'"
  local tmp; tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' RETURN
  split_findings "$findings" "$tmp"
  local nblocks; nblocks="$(ls "$tmp"/b*.txt 2>/dev/null | wc -l)"
  if [ "$nblocks" -eq 0 ]; then
    echo "k8a-sink: findings file has no disagreements; nothing to file"
    return 0
  fi
  [ -n "$existing" ] || { existing="$tmp/existing.tsv"; : > "$existing"; }
  if [ ! -f "$existing" ]; then
    if [ "$dry" -eq 1 ]; then : > "$existing"
    else
      gh issue list --label "$LABEL" --state open --limit 200 --json number,body \
        --jq '.[] | select(.body | test("k8a-sink-key: ")) | "\(.number)\t\(.body | capture("k8a-sink-key: (?<k>[^ ]+) -->").k)"' > "$existing" \
        || die "could not list open $LABEL issues"
    fi
  fi

  # group the blocks by key (first-seen order)
  local -a keys=()
  declare -A first=() also=()
  local i hdr seed prog variant shape p key
  for (( i = 1; i <= nblocks; i++ )); do
    hdr="$(head -1 "$tmp/b$i.txt")"
    seed="$(field seed "$hdr")"; prog="$(field prog "$hdr")"
    variant="$(field variant "$hdr")"; shape="$(field shape "$hdr")"
    p="$(pair < "$tmp/b$i.txt")"
    key="construct:k8a-gen/${shape#sh}|$row|$p"
    if [ -z "${first[$key]:-}" ]; then first[$key]="$i"; keys+=("$key")
    else also[$key]+="  - seed=$seed prog=$prog variant=$variant"$'\n'; fi
  done

  local n=0 num
  for key in "${keys[@]}"; do
    i="${first[$key]}"
    hdr="$(head -1 "$tmp/b$i.txt")"
    seed="$(field seed "$hdr")"; prog="$(field prog "$hdr")"
    variant="$(field variant "$hdr")"; shape="$(field shape "$hdr")"
    p="${key#*|}"; p="${p#*|}"
    num="$(awk -F'\t' -v k="$key" '$2 == k { print $1; exit }' "$existing")"
    local repro rows; repro="$(repro_cmd "$row" "$seed" "$prog")"
    rows="$(threeway_rows "$tw" "$seed" "$prog")"
    local body="$tmp/body$n.md"
    if [ -n "$num" ]; then
      {
        echo "Seen again on build row \`$row\`: seed=$seed prog=$prog variant=$variant."
        [ -z "$runurl" ] || echo "Run: $runurl"
        [ -z "${also[$key]:-}" ] || { echo; echo "Also:"; printf '%s' "${also[$key]}"; }
        echo; echo "Three-way row:"; echo '```'; echo "$rows"; echo '```'
        echo; echo "Repro:"; echo '```'; echo "$repro"; echo '```'
      } > "$body"
      if [ "$dry" -eq 1 ]; then
        echo "DRYRUN gh issue comment $num --body-file <body>"
        echo "---- body ----"; cat "$body"; echo "---- end ----"
      else
        gh issue comment "$num" --body-file "$body" || die "gh issue comment $num failed"
      fi
    else
      local rsrc="$tmp/red$n"
      if [ "$reduce" -eq 1 ]; then reduce_block "$seed" "$prog" "$variant" "$rsrc" "$backend" "$image" "$rounds"; fi
      local pr; pr="$p"
      [ ! -s "$rsrc.pair" ] || { pr="$(cat "$rsrc.pair")"; key="construct:k8a-gen/${shape#sh}|$row|$pr"; }
      local title="k8a differential: construct:k8a-gen/${shape#sh} on $row ($pr)"
      {
        echo "<!-- k8a-sink-key: $key -->"
        echo "A K8a differential disagreement, filed by scripts/k8a-sink.sh."
        echo
        echo "- cell: \`construct:k8a-gen/${shape#sh}\`"
        echo "- build row: \`$row\`"
        echo "- verdict pair: \`$pr\`"
        echo "- first seen: seed=$seed prog=$prog variant=$variant"
        [ -z "$runurl" ] || echo "- run: $runurl"
        if [ -n "${also[${key}]:-}" ]; then echo "- also this run:"; printf '%s' "${also[$key]}"; fi
        echo; echo "Three-way columns (release / head / native):"; echo '```'; echo "$rows"; echo '```'
        if [ -s "$rsrc.src" ]; then
          echo; echo "Reduced program:"; echo '```nim'; cat "$rsrc.src"; echo '```'
        fi
        echo; echo "Original finding (unreduced):"; echo '```'; sed 1d "$tmp/b$i.txt"; echo '```'
        echo; echo "Repro (the generator's suite at this seed):"; echo '```'; echo "$repro"; echo '```'
      } > "$body"
      if [ "$dry" -eq 1 ]; then
        echo "DRYRUN gh issue create --title '$title' --label $LABEL --body-file <body>"
        echo "---- body ----"; cat "$body"; echo "---- end ----"
        printf '%s\t%s\n' "$(( 9000 + $(wc -l < "$existing") ))" "$key" >> "$existing"
      else
        gh issue create --title "$title" --label "$LABEL" --body-file "$body" || die "gh issue create failed"
      fi
    fi
    n=$(( n + 1 ))
  done
  echo "k8a-sink: $nblocks finding(s), $n key(s)"
}

self_test() {
  local bad=0 got d
  eq() { [ "$2" = "$3" ] || { echo "self-test FAILED: $1: want '$3' got '$2'"; bad=1; }; }
  eq "sat miss" "$(printf 'x\nnative differential: pinExact construct:k8a-gen/DivLit: walker says sxSat for t but the witness does not hit natively: hits=[]' | pair)" "sxSat|native-miss"
  eq "unsat hit" "$(printf 'native differential: pinExact c: walker says sxUnsat for t but (1,1) hits it natively' | pair)" "sxUnsat|native-hit"
  eq "raised" "$(printf 'walker says sxRaised(OverflowDefect) but the witness natively did: x' | pair)" "sxRaised|native-mismatch"
  eq "meta" "$(printf 'metamorphic: original sxSat vs twin sxUnsat\n--- original\n' | pair)" "meta:sxSat|sxUnsat"
  eq "annotation" "$(printf 'annotationViolations: 2' | pair)" "annotation|-"
  d="$(mktemp -d)"
  : > "$d/empty.txt"
  eq "empty findings" "$(bash "$0" file --findings "$d/empty.txt" --row linux-c --dry-run 2>&1)" "k8a-sink: findings file has no disagreements; nothing to file"
  rm -rf "$d"
  [ "$bad" -eq 0 ] && echo "k8a-sink self-test: ok"
  return "$bad"
}

case "${1:-}" in
  file) shift; file_cmd "$@" ;;
  pair) pair ;;
  --self-test) self_test ;;
  *) die "usage: k8a-sink.sh file|pair|--self-test (see the header)" ;;
esac
