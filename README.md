# Verifying proofs in CS220 with Lean

Lean is an interactive theorem prover. Lean is a functional programming language with a type 
system powerful enough to express proofs.

You can get started with Lean at the home page https://leanprover-community.github.io/. You can 
even try it in your browser to avoid any installation process (click [Try the online version of Lean](https://live.lean-lang.org/) on the home page). Alternatively, follow [installation instructions](https://lean-lang.org/install/) and get set up in Visual Studio Code locally. Note that it might 
be wise to install Lean yourself rather than letting the VSCode extension do it for you, some of us
have had trouble where the automated installation fails.

We recommend [Theorem proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) as an
introductory text to get you started with the language.

# Install MathLib

To do math in lean, you will want *mathlib*. To install mathlib, run the following command on your terminal in the root of this git repo.

```bash
lake update
```

The VSCode extension may figure out how to do this for you without manual intervention.

# Next steps

Have fun learning Lean and mathematical proof! If there is a missing theorem that we prove in class,
please submit a PR.
