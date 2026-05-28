## proptest — property-based testing for Nim with internal choice-sequence shrinking.
##
## This is the package entry point. Implementation is built test-first; see the
## milestones/issues on the repository for the build order. Public API will be
## re-exported from here as each layer lands (DataSource & choice IR, strategies
## & combinators, the engine, the shrinker, the `given` DSL, auto-derivation, the
## example database, stateful and targeted testing).

const proptestVersion* = "0.1.0"

import proptest/[int128, choice]
export int128, choice
