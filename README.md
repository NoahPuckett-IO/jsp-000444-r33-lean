# JSP-000444: growth of the Ramsey number R(3,3,m) in Lean 4

This is a complete, `sorry`-free Lean 4 / Mathlib formalization of the answer to
[JSP-000444](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000444)
([Erdős Problem #553](https://www.erdosproblems.com/553)):

> How fast does the three-color Ramsey number grow for a triangle in either of the first two colors
> versus a large clique in the third?

**Answer (Alon–Rödl 2005):** R(3,3,m) = m³ · (log m)^{O(1)}. In particular R(3,3,m)/R(3,m) → ∞,
which is the Erdős–Sós conjecture asked on erdosproblems.com/553.

## Main theorem (`JSP444.lean`)

```lean
theorem JSP444.jsp_000444 :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ m : ℕ in atTop,
        c * (m : ℝ) ^ 3 / Real.log m ^ 6 ≤ R33 m ∧ (R33 m : ℝ) ≤ C * (m : ℝ) ^ 3) ∧
    Tendsto (fun m : ℕ => (R33 m : ℝ) / R3 m) atTop atTop
```

The definitions are self-contained, and only Mathlib is imported:

```lean
def MonoClique {N r : ℕ} (c : Sym2 (Fin N) → Fin r) (i : Fin r) (k : ℕ) : Prop :=
  ∃ s : Finset (Fin N), s.card = k ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → c s(x, y) = i
def Good33 (m N : ℕ) : Prop :=
  ∀ c : Sym2 (Fin N) → Fin 3, MonoClique c 0 3 ∨ MonoClique c 1 3 ∨ MonoClique c 2 m
def Good3 (m N : ℕ) : Prop :=
  ∀ c : Sym2 (Fin N) → Fin 2, MonoClique c 0 3 ∨ MonoClique c 1 m
noncomputable def R33 (m : ℕ) : ℕ := sInf {N | Good33 m N}   -- R(3,3,m)
noncomputable def R3  (m : ℕ) : ℕ := sInf {N | Good3 m N}    -- R(3,m)
```

Both `sInf` sets are proved nonempty (`good33`, `good3`), so the Ramsey numbers are genuine. `R3 m > 0` for `m ≥ 1` is proved too (`R3_pos`).

## Proof outline

The file has four parts.

1. **Upper bound (Part A).** A greedy independent-set lemma gives R(3,m) ≤ m(m−1)+1 and R(3,3,m) ≤ (2m(m−1)+1)(m−1)+1 ≤ 2m³. Every red or blue neighbourhood is a bad 2-colouring.
2. **Pseudorandom triangle-free graph (Part B).** Let F be a finite field of characteristic 2 with |F| = q, and φ : F → 𝔽₂ a nonzero additive map.
   - Let S = { x·(y, y², y³) : φ(x) = 1, y ≠ 0 } ⊂ F³. The Cayley graph G on F³ with generating set S is triangle-free, by a Vandermonde-type identity.
   - Its eigenvalues satisfy |λ| ≤ 6|T| = 3q, by ±1 characters and the fact that a cubic has at most 3 roots.
   - Parseval then gives Alon–Rödl's Lemma 2.2: few vertices of any B have few neighbours in B.
3. **Counting (Part C).**
   - A Kleitman–Winston-type bound on the number of independent m-sets (Alon–Rödl Theorem 2.1).
   - A permutation-averaging lemma, the deterministic form of Alon–Rödl Lemma 3.1: if |I|² < C(n,m), some permutation moves every independent m-set off the family.
4. **Assembly (Part D).**
   - With q = 2^k, n = q³ and M = q·2¹⁴·k², colour 0 is G and colour 1 is a permuted copy of G. This gives R(3,3,M) > 2^{3k} for k ≥ 12. It is instantiated with `GaloisField 2 k`.
   - Interpolating over m gives c·m³/(log m)⁶ ≤ R(3,3,m), with c = 2^{-57}.

The construction of the pseudorandom graph differs from the one in Alon–Rödl (Alon's graph), and it keeps every proof step elementary. The overall method is Alon–Rödl's.

## Build

```sh
lake exe cache get
lake build
lake env lean AxiomCheck.lean
```

Expected output:

```
'JSP444.jsp_000444' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Toolchain: `leanprover/lean4:v4.35.0-rc2`. Mathlib: tag `v4.35.0-rc2` (commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`).
The source contains no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe`.

## Attribution

- **Mathematics:** Noga Alon and Vojtěch Rödl, *Sharp bounds for some multicolor Ramsey numbers*,
  Combinatorica 25 (2005) 125–141, [doi:10.1007/s00493-005-0011-9](https://doi.org/10.1007/s00493-005-0011-9)
  ([author PDF](https://web.math.princeton.edu/~nalon/PDFS/arodl4.pdf)). The problem is due to Erdős and Sós.
- **Lean formalization:** NoahPuckett-IO, with AI assistance (Claude). It is written from scratch and reuses no code
  from other formalization projects.
