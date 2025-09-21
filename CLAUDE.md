# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Development Environment

This is a Lean 4 mathematical textbook/tutorial project using:
- **Lean version**: 4.22.0 (specified in lean-toolchain)
- **Build system**: Lake (Lean's package manager and build tool)
- **Nix support**: Available via flake.nix for reproducible development environment

## Key Commands

### Building
- `lake build` - Build the entire project
- `lake build LeanBook` - Build the main library
- `lake build <ModuleName>` - Build a specific module (e.g., `lake build LeanBook.Logic.CH`)

### Development
- `lake lean <file.lean>` - Elaborate a specific Lean file in Lake's context
- `lake env <command>` - Execute command in Lake's build environment
- `lake clean` - Remove build outputs

### Package Management
- `lake update` - Update dependencies and manifest
- `lake check-build` - Verify build targets are configured

## Project Structure

### Architecture Overview
This is an educational Lean 4 project structured as a mathematical textbook with progressive chapters:

1. **FirstProof/**: Introduction to proofs and natural numbers
   - Custom `MyNat` inductive type implementation
   - Basic arithmetic operations and proofs

2. **Logic/**: Logical foundations and proof techniques  
   - Propositional logic (`PropLogic.lean`)
   - Predicate logic (`PredLogic.lean`) 
   - Classical logic concepts (Choice, Excluded Middle)
   - Dependent types (`Dependent.lean`)

3. **NatCommMonoid/**: Natural number algebraic structures
   - Type class implementations (`TypeClass.lean`)
   - Induction principles (`Induction.lean`, `BetterInduction.lean`)
   - Simplification tactics (`Simp.lean`)
   - Reflexivity and commutativity (`AcRfl.lean`)

4. **NatSemiring/**: Semiring structure for natural numbers
   - Multiplication operations and proofs (`Mult.lean`)

### Module Organization
- **Root module**: `LeanBook.lean` imports `LeanBook.Basic` (imports structured under `LeanBook/` directory)
- **Naming**: Files use descriptive names in both English and Japanese comments
- **Dependencies**: Each module imports necessary foundations from earlier chapters

### Code Patterns
- Heavy use of Japanese comments for mathematical explanations
- Custom inductive types with corresponding type class instances
- Pattern matching with `.` syntax for constructors
- Extensive use of `by rfl` for definitional equality proofs
- `#eval` and `#check` commands for verification and exploration

## Development Notes

- This project teaches Lean 4 through implementing mathematical concepts from scratch
- Custom implementations often parallel standard library types (e.g., `MyNat` vs `Nat`)
- Type class instances are implemented to enable familiar notation (`+`, numerals)
- Proofs progress from simple reflexivity to more complex inductive arguments

## Guidelines

When solving problems, strictly follow this workflow. Especially adhere to the rule in Step 3: "edit sections must be within 5 lines":

1. **Maximize reasoning** and think about how to solve the problem, writing a natural language proof sketch as comments. Do not write any Lean code at this stage.

2. **Return reasoning to normal** and decompose the problem into subgoals using `have` or `lemma` (and `suffices`, `refine`, `by_cases`, `rcases` etc. as needed) based on the above sketch. Do not write the actual proof content - fill with `sorry`. Keep the proof sketch as comments. Always verify that the build passes.

3. **Keep reasoning normal** and replace the first `sorry` (from file beginning) with actual proof. However, proof blocks must be within 5 lines (as file lines), and each edit must also be within 5 lines (as file lines). Cramming everything into one line to meet the 5-line limit is prohibited (write normal Lean code). If more than 5 lines are needed, recursively apply Steps 1-2 to this subproblem to further divide it (during subdivision (recursive Steps 1-2), line count constraints don't apply, but follow each step's content requirements). Always verify build passes after each edit.

### Proof Strategies

- **Inline lemmas**: Use `rw [show <theorem> from by <proof>] at h` to create and apply supporting lemmas directly within rewrite steps. This adds new hypotheses to the local context without defining separate lemmas. Use for short proofs.
- **Adding hypotheses**: Use `have` to prove intermediate lemmas of reasonable length, which adds them as new hypotheses to the local context. This is useful for building up complex proofs step by step. Use for longer proofs than inline lemmas.

4. If `sorry` still remains, return to Step 3.

## Tools

- Use lean-lsp-mcp extensively
  - Use for type checking via hover, definition jumping, detecting unresolved meta-variables/sorries, type verification equivalent to #check, and extracting minimal reproductions during debugging.
- Also use lean-lsp-mcp for debugging
