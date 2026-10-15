# Lean self-check report: JSP-000444 (lean-verify method)

**Verdict: Verification passed.** The checks covered static review, a clean build with the pinned toolchain and Mathlib, `#print axioms`, and statement-correspondence review. No external checker (lean4checker or Comparator) was run.

Checked artifact: this folder, file `JSP444.lean` (1593 lines, sha256 `6853c1a8e16ca166f3feeaadf25e7b55b2174819656a1407300ea785f5bfdd91`).
- Submitted commit: `f3177cade914b990fa37bcf0ebffe0dcfe0eafce`, containing this exact file. Submitted as [TheJustinSunPrize/awards#5065](https://github.com/TheJustinSunPrize/awards/pull/5065).

Date: 2026-10-14.

## Four required answers

| Question | Answer | Evidence |
|---|---|---|
| 1. Does the proof address the original problem? | **Yes** | The catalog asks how fast R(3,3,m) grows. The theorem proves c·m³/(log m)⁶ ≤ R(3,3,m) ≤ C·m³ eventually, i.e. Θ̃(m³), which is Alon–Rödl's answer. It also proves R(3,3,m)/R(3,m) → ∞, which is Erdős #553 as stated. |
| 2. Did the checked version pass verification? | **Yes** | Fresh copy at `C:\Users\noahp\jv\jsp444`, `lake update` + `lake exe cache get` + `lake build`: "Build completed successfully (8932 jobs)". Mathlib HEAD is `065356127b1dc0016f66b7283ce0ce2c4055aa55` (v4.35.0-rc2). Log: `clean_build.log`. |
| 3. Does it fully solve the original problem? | **Yes** | Both the growth-rate statement and the ratio limit are proved, with no hypotheses on the main theorem. |
| 4. Does it meet the Lean completeness requirements? | **Meets** | `#print axioms JSP444.jsp_000444` gives `[propext, Classical.choice, Quot.sound]`. The source contains none of `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`. |

## Statement correspondence

| Original requirement | Lean | Correspondence |
|---|---|---|
| 3-colourings of the edges of K_N | `c : Sym2 (Fin N) → Fin 3`; only pairs with `x ≠ y` are ever read | Exact. Diagonal values are irrelevant. |
| Monochromatic triangle in colour 1 or 2 | `MonoClique c 0 3 ∨ MonoClique c 1 3` (3 distinct vertices, all pairs that colour) | Exact. |
| Monochromatic K_m in colour 3 | `MonoClique c 2 m` | Exact. |
| R(3,3,m) = least such N | `R33 m := sInf {N | Good33 m N}`. The set is nonempty (`good33`), so `sInf` is attained (`Nat.sInf_mem`). | Exact. No junk `sInf ∅ = 0`. |
| R(3,m) | `R3 m := sInf {N | Good3 m N}`, nonempty (`good3`), positive for m ≥ 1 (`R3_pos`) | Exact. |
| "How fast does it grow": R(3,3,m) = m³·(log m)^{O(1)} | `∃ c C > 0, ∀ᶠ m, c·m³/(log m)⁶ ≤ R33 m ∧ R33 m ≤ C·m³` | Equivalent to the Θ̃(m³) answer. Here c = 2^{-57} and C = 2. |
| Erdős–Sós: R(3,3,m)/R(3,m) → ∞ | `Tendsto (fun m => (R33 m : ℝ) / R3 m) atTop atTop` | Exact. |

## Trust and independence

- The only dependency is Mathlib, with no other packages. No code, definitions or statements are taken from plby/lean-proofs or any other formalization project.
- The lower-bound graph is an explicit Cayley graph on 𝔽_{2^k}³. Its triangle-freeness and eigenvalue bound are proved in the file.
- The finite field is `GaloisField 2 k`. A nonzero 𝔽₂-linear functional is obtained from `Module.forall_dual_apply_eq_zero_iff`.

## Limitations

- No `lean4checker --fresh` or Comparator run was done.
- The build was on Windows 11; any Linux-specific behaviour is untested.
