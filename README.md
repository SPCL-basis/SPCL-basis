# Natfunbasis

The main theorems are in `Natfunbasis/MainTheorems.lean` and
`Natfunbasis/Corollaries.lean`, in the namespace `Natfunbasis.Main`:

- `Main.addAtomic_iff_isBasis`: a natural function is +-atomic if and only if it is a finite product of towers;
- `Main.exists_basisSum_unique`: every natural function is, uniquely up to order, a sum of finite products of towers;
- `Main.pow_addAtomic`, `Main.pow_input_addAtomic`: f^g is +-atomic when g is nonconstant and +-atomic;
- `Main.basis_linearIndependent`: distinct finite products of towers are linearly independent over the reals.

These theorems carry no hypotheses and use only Lean's standard axioms.

## Build

Lean `v4.32.2`, Mathlib `v4.32.2`.

```
lake exe cache get
lake build
```
