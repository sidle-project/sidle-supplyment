# SIDLE Supplemental Materials

This directory hosts companion materials for the SIDLE project.

## Contents
- [appendix.pdf](appendix.pdf): Implementation details of the SIDLE framework, along with guidelines for user integration, a worked example, and guidance on migration under different concurrency strategies.
- [tla/](tla/): TLA+ models and configurations that provide correctness proofs for migrations across multiple concurrency strategies.

### TLA+ assets
- [tla/lockfree.tla](tla/lockfree.tla) with [tla/lockfree.cfg](tla/lockfree.cfg): Proof artifacts for migrations under lock-free concurrency.
- [tla/occ.tla](tla/occ.tla) with [tla/occ.cfg](tla/occ.cfg): Proof artifacts for migrations using optimistic concurrency control.
- [tla/rwlock.tla](tla/rwlock.tla) with [tla/rwlock.cfg](tla/rwlock.cfg): Proof artifacts for migrations with read-write locking strategies.

## Purpose
Use these resources alongside the main SIDLE artifacts to understand the framework internals and to validate migration procedures under varying concurrency models.
