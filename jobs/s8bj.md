# Job: S8bj -- resume slice (S8bb's remainder B)

Branch `rfc-0005-s8bj`, checkpoint 8bb291b (base 9e15103 = rfc-0005-s8bb). Walker target is 211.
Resume it in a worktree at origin/rfc-0005-s8bj. Read WORKER-BRIEF.md first. This is the hardest open slice. Use your strongest model, and plan before coding.

## Scope (do all of it; defer nothing)

Ground truth is PCRE 8.45 as `std/re` calls it. A differential harness checks the real `std/re` against the model on enumerated small inputs. Every feature you model must agree on every input.

1. **Backtracking verbs and start options.**
   - Verbs: (*COMMIT), (*PRUNE), (*SKIP) and (*SKIP:NAME), (*THEN).
   - Start options: (*LIMIT_MATCH=) and (*LIMIT_RECURSION=).
   - PCRE's start optimiser runs as a start-position filter ahead of the verb semantics.
   - Model a LIMIT error exactly where you can compute it; otherwise make it a scoped decline with a named reason.
2. **UTF mode under the byte-faithful string model.**
   - Chars ≤ 0xFF equal Nim bytes. This is Corey-locked.
   - An invalid subject gets PCRE's error result.
3. **(?m) and (?X).**
   - (?m): line-boundary ^ and $ under each newline convention.
   - (?X): compile-time RegexError parity.
4. **The (*CRLF) start-position skip.** This removes `crlfSkipSeen`.
5. **Decide symbolic replace Q2, Q7 and Q8** (from S8bb's table) within budget on both Z3 versions, measured before and after. The exact cases that already work must not regress.

**Tests:** `tests/tsymex_rfc0005_s8bj_*.nim`, split by feature so each file stays under 60 s per backend on Windows. Register every file in nelli.nimble.

**Verification:** your suites, every s8bb suite, s8ay, s8aw, S6a, S6b, CR10, s5_str, s6b_ops, S7b_smoke and CR2. Run all of them on Z3 5.1 and 4.13.4, run one suite in cpp, then the three Windows legs. Report DONE as worker-reports/s8bj.md.

## Handoff note from the previous agent

S8bj is handed off at checkpoint **`8bb291b`**, pushed to `origin/rfc-0005-s8bj`. That sha includes the differential harness. Base is `origin/rfc-0005-s8bb` at 9e15103. The walker is still 201 (the target is 211). No implementation code is written yet: this checkpoint holds research, probe data and the pending RFC row only.

I had no test runs going, so there was nothing to kill. The running podman processes all belong to other worktrees (`agent-aec7…`, `agent-a2d9…`).

## Done
- **10ef8cf**: the S8bj row (`state = "pending"`) is in `docs/rfc/0005-branch-scoped-degrade.md`, between S8bb and S11.
- **8bb291b**: the probe harness is in `tests/s8bj_harness/`. The file names don't start with `t`, so the sweep ignores them.
  - `pc.nim` is a compile probe: it prints each pattern's `RegexError` first line and caret offset. Its corpus is `pc1.txt` and the Linux 8.45 results are in `pc1.linux-8.45.out`.
  - `p2.nim` is an exec probe over all subjects up to a given length (find / matchLen / findBounds.last / replace). `p2_limit.txt` is an input for it.
  - `p2.sh <worktree> <prog> <input>` compiles a probe in podman, caches the binary under `scratch/`, and runs it.
  - `probe_s8bj_pcre.nim` hashes every entry point per pattern and dumps PCRE's start-optimiser data as `INFO` lines: anchored, first char, required char, min length, HASCRORLF, start bits. Those lines are extracted into `fullinfo-linux-8.45.txt` and `fullinfo-windows-8.37.txt` (184 patterns). The two files are identical apart from the version/JIT line, so they can serve as the oracle for the start-optimiser inference.
- The throwaway branch `rfc-0005-s8bj-probe` (0d14931) has a symex-mingw job that runs `tests/tprobe_s8bj_*.nim` on Windows. Reuse it for Windows probes, then delete it from the remote at the end.

## RED / GREEN pins
None yet. No `tests/tsymex_rfc0005_s8bj_*.nim` file exists. The `crlfSkipSeen` pins in `tests/tsymex_rfc0005_s8bb_constructs.nim` (lines 242–401) and `tests/tsymex_rfc0005_s5_str.nim:338` are expected to change once the CRLF-skip decline is removed.

## What I learned

**`std/re` (Nim 2.2.10)**
- `re()` compiles with no flags, then calls `pcre.study` with the JIT flag when JIT is available.
- `matchLen`, `match`, `startsWith` and `endsWith` pass ANCHORED; find, findBounds, contains and replace do not.
- How errors surface:
  - `matchLen` and `find` return the raw negative code.
  - `match` is `matchLen != -1`, so an error reads as true.
  - `contains` is `find >= 0`.
  - Plain `findBounds` returns `(code, 0)`; the captures `findBounds` and `findBoundsImpl` (used by replace) return `(-1, 0)`.
  - `startsWith` is `matchLen >= 0`.
  - `endsWith` loops `i in 0..len-1` testing `matchLen(s, re, i) == len - i`.
- `replace` loop: `prev = last + 1`, with NOTEMPTY_ATSTART after an empty match. On a UTF error the first call returns `(-1, 0)`, so replace returns the subject unchanged.

**Platforms**
- Linux runs PCRE 8.45 without JIT. Windows CI runs 8.37 with JIT: anchored calls use the interpreter, unanchored calls use the JIT.
- They diverge only on:
  - LIMIT with unanchored calls (11 patterns): the JIT ignores LIMIT_RECURSION and LIMIT_MATCH=0, and counts LIMIT_MATCH differently.
  - `(*CRLF)\s(*SKIP)b` on length-3 subjects. This still needs a targeted Windows probe.

**Compile facts (all probed; offsets are in `pc1.linux-8.45.out`)**
- **Verbs**
  - Verb names are uppercase only. A bad or unknown verb is "(*VERB) not recognized or malformed" at the offset where the letter run ends.
  - COMMIT, ACCEPT and F with an argument → "an argument is not allowed …"; MARK without one → "(*MARK) must have an argument".
  - `(*PRUNE:)`, `(*SKIP:)` and `(*THEN:)` are OK.
  - A quantifier after a verb → "nothing to repeat".
  - `(*1)` and `(* COMMIT)` are "nothing to repeat" at offset 1.
- **LIMIT**
  - Only valid as a start option. Digits are read with the overflow guard `c > 429496728`, so `4294967295` is rejected as a bad verb at offset 7.
  - `(*LIMIT_MATCH=)` means 0. The smallest limit given wins (`c < limit`).
  - It mixes freely with `(*UTF8)` in either order.
- **UTF**
  - An invalid UTF-8 pattern → "invalid UTF-8 string" at the bad byte's offset.
  - `\x{d800}` → "disallowed Unicode code point …"; `\x{110000}` → "character value in \x{} or \o{} is too large".
  - Without UTF, `\x{100}` is too large and `\400` → "octal value is greater than \377 …".
  - UCP support is compiled in: `(*UTF8)\p{L}` is OK. So UTF+caseless folds k/s through the Unicode case sets (U+212A, U+017F); decline those.
- **`\L \l \U \u \N{x}`** always reject with "PCRE does not support \L, \l, \N{name}, \U, or \u", at the offset of the letter, also inside a class.
- **`(?X)`**
  - It rejects "unrecognized character follows \" at the letter for i j m q y F I J M O T Y, inside and outside classes.
  - It is scoped like the other options, ending at the group's close (`(?:(?X))\i` is OK), and it carries across later alternatives (`a(?X)|\i` is rejected).
  - `\8`, `\9` and `\_` stay OK.
- **`(?m)`** parses with no errors anywhere.

**Start optimiser (read from `pcre_compile.c` and `pcre_exec.c`)**
- Verbs other than ACCEPT do not reset firstchar, so `(*COMMIT)abc` gets first char `a`. The `fullinfo` data confirms this (`fc=97 rc=99 min=3`).
- `set_start_bits` fails on every verb.
- After `(*ACCEPT)` the required char is disabled.
- A class with exactly one member becomes OP_CHAR (sets firstchar) or OP_NOT (does not).
- A zero-minimum repeat restores the saved first/required chars.
- Combining alternatives: a differing firstchar becomes NONE, and the old firstchar becomes the required char.
- The search-loop order is: first char → startline (only past the start offset; ANY/ANYCRLF also skip the LF after a CR) → start bits → minlength break → required-char break (subjects under 1000 bytes) → attempt.
- After the attempt:
  - SKIP_ARG re-runs at the same start with `ignore = skip_arg_count`.
  - SKIP jumps only forward.
  - NOMATCH, PRUNE and an uncaught THEN bump by 1 (by a whole character under UTF).
  - COMMIT ends the search with no match.
  - Then the loop breaks if the call is anchored.
  - Then the CRLF skip: past the start offset, `[-1]==CR`, `*s==LF`, no explicit CR/LF in the pattern, and a newline convention of ANY, ANYCRLF or CRLF.
- A THEN is caught by any bracket frame with at least 2 alternatives where the THEN's address is before that branch's end. A frame left on the stack by an earlier loop iteration can therefore catch it; decline that case.

**Design** (settled in the previous context; the full text is in the session transcript)
- The attempt runs as an ordered item list:
  - threads, each with a state and a THEN context;
  - a MATCH item that cuts everything after it;
  - COMMIT, PRUNE, SKIP(marker) and THEN(target) sentinels, emitted after the verb's continuation;
  - one ALTEND marker after each alternative of a multi-alternative group.
- The search machine keeps an ordered list of runs and markers, filters start positions, and applies the CRLF skip.
- `(?m)` needs a prior-byte context: start / CR / LF / other newline / other.
- UTF matches characters as byte sequences, checks the whole subject for validity (-10) and rejects a start offset inside a character (-11).
- LIMIT 0 is an error exactly when an attempt is made. A limit at or above a static bound on a loop-free pattern counts as no limit. Anything else declines, and on Windows the unanchored LIMIT_MATCH ≥ 1 case declines.
- Replace Q2, Q7 and Q8 get sound lemmas:
  - the image of replace as a regular language;
  - a length relation `len(r) = len(s) - c + k·|by|`, with `k·mn ≤ c ≤ k·mx`.

**Dead ends:** none in code. One fact disproved: the first char does not drive the filter in general. The filter only changes a result through a COMMIT reached before anything is consumed, the CRLF skip, LIMIT, or a SKIP:NAME re-run at an LF after a CR.

## Next steps
1. Parser (`src/nelli/smt/pcre_syntax.nim`):
   - verbs as tree nodes, keeping their names for SKIP:NAME;
   - LIMIT values;
   - UTF mode, with each atom's compiled opcode recorded (char, not-char, class, escape type, any);
   - multiline `^`/`$` kinds;
   - `(?X)` with scoping;
   - the `\L` family.

   Test it with `tests/tsymex_rfc0005_s8bj_syntax.nim`, diffing the messages and offsets in `pc1.linux-8.45.out` against the real `re()`.
2. Port PCRE's first/required-char logic, `is_anchored`, `is_startline`, `set_start_bits` and `find_minlength` over the tree. Pin them against `pcre.fullinfo`, using the `INFO` lines as a corpus.
3. Build the attempt machine in `src/nelli/smt/pcre_select.nim` (`closure`, `buildDfa`, `chosenEnd`), then the search machine (replacing `searchDfa`). Remove `crlfSkipSeen`, and give replace a search step table in `src/nelli/smt/regex_parser.nim` (`replaceRunZ3`).
4. Then `(?m)`, UTF, LIMIT, and the replace lemmas, measuring Q2/Q7/Q8 before and after on Z3 5.1 and 4.13.4.
5. Bump the walker to 211, update and run `tests/tsymex_phase15_CR2_cachekey.nim`, and add the `>= 211` floor.
6. Run the verification suites on both Z3 versions plus one cpp run, push for the three Windows legs, and write "As landed (S8bj)".

The remote worker needs its own PCRE 8.45 source tree, which is not in the repo. The `std/re` source is at `/opt/nim/2.2.10-patched/lib/impure/re.nim` inside `localhost/nelli-dev`.
