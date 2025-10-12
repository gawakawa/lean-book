# LeanBook

Learning materials for the book『[ゼロから始めるLean言語入門 ― 手を動かして学ぶ形式数学ライブラリ開発](https://www.lambdanote.com/products/leanbook)』.

## Requirements

- Nix (with flakes enabled)
- direnv (optional)

## Setup

```bash
nix develop
```

With direnv, the environment is automatically loaded when entering the directory.

## Usage

```bash
lake build
```

## Directory Structure

```
LeanBook/
├── FirstProof/       # Introduction to proofs and natural numbers
├── Grind/            # Grind tactic examples and applications
├── Int/              # Integer construction via quotients and setoids
├── IntMathlib/       # Integer arithmetic and ordering (Mathlib-style)
├── Logic/            # Propositional and predicate logic, classical axioms
├── NatCommMonoid/    # Natural numbers as commutative monoid with type classes
├── NatOrder/         # Ordering relations on natural numbers
└── NatSemiring/      # Semiring structure: multiplication and distributivity
```
