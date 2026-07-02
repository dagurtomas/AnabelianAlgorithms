# AnabelianAlgorithms

Private local extraction of the Lean algorithm/example files from `Anabelian` that are ready for
separate review.  This repository is not configured with a remote and has not been published.

It depends on the public GitHub copy of `AnabelianLib` at commit
`2144477d31ca4d816a67e29d7886efba8ae14bb2`; mathlib is inherited transitively through that
dependency.

Included entry points:

- `AnabelianAlgorithms.Examples.NeukirchUchidaLeanEval`
- `AnabelianAlgorithms.Examples.MochizukiLocalProP.ProperHyperbolicCurveHomStandalone`

The supporting files under `AnabelianAlgorithms/Mathlib/FromPi1` are copied and adapted from
Christian Merten's `pi1` project (<https://github.com/chrisflav/pi1>), commit
`5c5c0171efc863ce9990171bdf46d7cb5fd582fb`, with the original attribution headers preserved in
the individual files.

Lean declarations mostly keep their original `Anabelian` namespaces for continuity with the source
repository, while module names live under `AnabelianAlgorithms`.
