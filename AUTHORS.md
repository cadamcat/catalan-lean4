# Authors and attribution

Yao Xu ([@cadamcat](https://github.com/cadamcat)) is the author and maintainer of this formalization project.

The mathematical theorem was proved by Preda Mihăilescu. This repository formalizes the theorem; it does not claim a new mathematical solution. The proof development follows the cyclotomic and class-field-theoretic approach, including Yuri Bilu's exposition.

The author planned, dispatched and reviewed the work. GPT-6 Pro sessions in ChatGPT produced informal blueprints and draft Lean statements, which were treated as unverified input. Formalization and review used GPT-6 Astra and GPT-5.6 Luna in Codex, and Fable 5.1 and Opus 5 in Claude Code. The resulting proofs and their dependencies were checked by the Lean kernel. The October 2026 port to Lean v4.35.0-rc3 and the module system (release v1.1.0), a mechanical update with unchanged theorem statements, was done with GPT-6 Luna in Codex.

The project uses Mathlib and a fixed subset of ClassFieldTheory. Their authors and licenses remain credited in [THIRD_PARTY.md](THIRD_PARTY.md) and the vendored sources.
