## Auto-label sink for #108 — strategy distribution observability.
##
## Strategies are leaf-level (no engine deps). The engine, by contrast,
## owns the frame where categorical events get recorded. To let strategies
## emit auto-labels without inverting that dep, we use a threadvar
## proc-pointer sink: strategies call `autoLabel(label)` unconditionally,
## the sink either swallows the call (nil = no sink installed, e.g. raw
## `s.generate(...)` outside any forAll) or routes it into the engine's
## current frame.
##
## The engine installs the sink in `runForAllPipeline` (similar discipline
## to coverage mode) when `Settings.autoLabels` is on, and restores the
## prior sink on exit — so nested forAll calls compose.
##
## All built-in strategies emit labels under the reserved `auto.` prefix
## (e.g. `auto.int:near-lo`, `auto.list-len:empty`) so user `event()`
## calls can't collide.

const autoLabelPrefix* = "auto."
  ## Reserved prefix for engine-emitted distribution labels. Users
  ## filter their categorical histograms by `.startsWith(autoLabelPrefix)`
  ## to separate auto-labels from manually-emitted events.

type AutoLabelSink* = proc(label: string) {.nimcall.}

var autoLabelSink {.threadvar.}: AutoLabelSink

proc setAutoLabelSink*(sink: AutoLabelSink) =
  ## Install (or clear, with `nil`) the per-thread auto-label sink.
  ## The engine flips this on at the start of a `runForAllPipeline`
  ## run (when `Settings.autoLabels` is on) and restores the prior
  ## value on exit.
  autoLabelSink = sink

proc currentAutoLabelSink*(): AutoLabelSink =
  ## Snapshot the current sink; used by the engine to save-and-restore
  ## across nested runs.
  autoLabelSink

proc autoLabel*(label: string) {.inline.} =
  ## Emit a categorical event under the current sink. No-op when no
  ## sink is installed (raw strategy use outside forAll, or
  ## `Settings.autoLabels=false`).
  if autoLabelSink != nil:
    autoLabelSink(label)
