# DBSP formalization

[![CI](https://github.com/tchajed/database-stream-processing-theory/actions/workflows/lean_build.yml/badge.svg)](https://github.com/tchajed/database-stream-processing-theory/actions/workflows/lean_build.yml)

Lean formalization of the theory behind [DBSP](https://arxiv.org/abs/2203.16684), a
language for expressing incremental view maintenance for databases.

DBSP can be divided into two parts: a general theory of operators over streams,
and a specialization of that theory to implement relational algebra queries.

## Defining the basic DBSP operators

- [stream.lean](src/stream.lean) defines infinite streams over an arbitrary type `a` as `ℕ → a`.
- [operators.lean](src/operators.lean) defines the notion of an operator (a
  function between streams) and properties of operators (like causality,
  strictness). It defines three core operators: the pointwise lifting of a
  function, the delay operator `z⁻¹`, and a general fixpoint construction for
  constructing a stream recursively.
- [linear.lean](src/linear.lean) defines the differentiation and integration
  operators for streams over an arbitrary group, and the associated property of
  linearity.
- [incremental.lean](src/incremental.lean) defines the core DBSP idea of the
  incrementalization `Q^Δ` of an operator `Q`, defind as `D ∘ Q ∘ I`. It also
  has proofs of an equational theory of incrementalization.
- [circuits.lean](src/circuits.lean) defines a "circuit", which is a restricted
  language for defining operators. We can define and prove correct a general
  algorithm for incrementalizing and optimizing any circuit, and thus any operator
  expressible as a circuit.

## Relational algebra in DBSP

- [zset.lean](src/zset.lean) defines Z-sets, a generalization of multisets used
  to model relations and changes to relations. A Z-set `Z[A]` over a type `A` is
  a function from `A` to integers `ℤ` with finite support: only finitely many
  elements map to non-zero integers.
- [relational.lean](src/relational.lean) defines versions of the basic
  relational operators over Z-sets, and proves that they implement the set
  versions of the operators in an appropriate sense. This includes the
  DBSP-specific `distinct` operator, used to convert a Z-set to a set.
- [relational_incremental.lean](src/relational_incremental.lean) proves some
  rules for the incremental version of relational operators (perhaps most
  interestingly, of the lifted distinct operator).
- [relational_example.lean](src/relational_example.lean) is a self-contained
  file that works through an example of optimizing a relational query and its
  incremental version.
- [stream_elim.lean](src/stream_elim.lean) defines stream introduction and
  elimination functions `δ0` and `∫`. Stream elimination is complicated because
  it is only computable for streams that are zero almost everywhere.
- [recursive.lean](src/recursive.lean) defines and proves the correctness of a
  circuit that implements the recursive version of a relational query. This uses
  the stream introduction and elimination functions to create a new time domain,
  which we can think of as successive iterations of the recursion (rather than
  the usual notion of time).
- [aggregation.lean](src/aggregation.lean) defines the count and sum
  aggregations, which go from a Z-set to a number.

## Contributing

The DBSP team welcomes contributions from the community. Before you start working on this project, please
read our [Developer Certificate of Origin](https://cla.vmware.com/dco). All contributions to this repository must be
signed as described on that page. Your signature certifies that you wrote the patch or have the right to pass it on
as an open-source patch. For more detailed information, refer to [CONTRIBUTING.md](CONTRIBUTING.md).

## License

Copyright 2022-2023 VMware, Inc.

SPDX-License-Identifier: BSD-2-Clause

See [NOTICE](NOTICE) and [LICENSE](LICENSE).
