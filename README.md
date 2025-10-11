# LeanBook

Learning materials for the book『ゼロから始めるLean言語入門 ― 手を動かして学ぶ形式数学ライブラリ開発』(https://www.lambdanote.com/products/leanbook).

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
├── FirstProof/
├── Logic/
├── NatCommMonoid/
├── NatSemiring/
├── NatOrder/
├── Int/
└── IntMathlib/
```
