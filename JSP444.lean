import Mathlib

/-
JSP-000444 — the three-colour Ramsey number R(3,3,m) (Erdős Problem #553, Erdős–Sós).

Main theorem `JSP444.jsp_000444`:
* there are constants c, C > 0 with  c·m³/(log m)⁶ ≤ R(3,3,m) ≤ C·m³  for all large m
  (so R(3,3,m) = m³·(log m)^{O(1)}, the answer of Alon–Rödl, Combinatorica 25 (2005) 125–141);
* consequently R(3,3,m)/R(3,m) → ∞ (the Erdős–Sós conjecture).

Ramsey numbers are defined from scratch (`R33`, `R3`) via colourings `Sym2 (Fin N) → Fin r`.
The lower bound follows the Alon–Rödl method (count independent sets in a pseudorandom
triangle-free graph, then superimpose two random copies), using an explicit triangle-free Cayley
graph on 𝔽_{2^k}³ whose triangle-freeness and eigenvalue bound are proved here directly.
The upper bound is the elementary degree/greedy argument.
-/


open Finset

namespace JSP444

/-- The colouring `c` of the pairs of `Fin N` has `k` vertices whose pairs all get colour `i`. -/
def MonoClique {N r : ℕ} (c : Sym2 (Fin N) → Fin r) (i : Fin r) (k : ℕ) : Prop :=
  ∃ s : Finset (Fin N), s.card = k ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → c s(x, y) = i

/-- Every 3-colouring of `K_N` has a triangle in colour 0 or 1, or a `K_m` in colour 2. -/
def Good33 (m N : ℕ) : Prop :=
  ∀ c : Sym2 (Fin N) → Fin 3, MonoClique c 0 3 ∨ MonoClique c 1 3 ∨ MonoClique c 2 m

/-- Every 2-colouring of `K_N` has a triangle in colour 0 or a `K_m` in colour 1. -/
def Good3 (m N : ℕ) : Prop :=
  ∀ c : Sym2 (Fin N) → Fin 2, MonoClique c 0 3 ∨ MonoClique c 1 m

/-- The Ramsey number `R(3,3,m)`. -/
noncomputable def R33 (m : ℕ) : ℕ := sInf {N | Good33 m N}

/-- The Ramsey number `R(3,m)`. -/
noncomputable def R3 (m : ℕ) : ℕ := sInf {N | Good3 m N}

/-- Greedy independent sets: if inside `U` every vertex is `r`-related to at most `D`
members of `U`, then `U` contains a pairwise unrelated `S` with `|U| ≤ (D+1)|S|`. -/
theorem greedy {V : Type*} [DecidableEq V] (r : V → V → Prop) [DecidableRel r]
    (hsymm : ∀ x y, r x y → r y x) (D : ℕ) :
    ∀ U : Finset V, (∀ v ∈ U, (U.filter (r v)).card ≤ D) →
      ∃ S ⊆ U, (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ r x y) ∧ U.card ≤ (D + 1) * S.card := by
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
    intro hU
    rcases U.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · exact ⟨∅, by simp, by simp, by simp⟩
    set U' := (U.erase v).filter (fun w => ¬ r v w) with hU'
    have hsub : U' ⊂ U :=
      (Finset.filter_subset _ _).trans_ssubset (Finset.erase_ssubset hv)
    obtain ⟨S', hS'U, hS'ind, hS'card⟩ := ih U' hsub (fun w hw =>
      le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hsub.subset))
        (hU w (hsub.subset hw)))
    have hmem : ∀ w ∈ S', w ≠ v ∧ ¬ r v w := by
      intro w hw
      have := hS'U hw
      simp only [hU', Finset.mem_filter, Finset.mem_erase] at this
      exact ⟨this.1.1, this.2⟩
    have hvS' : v ∉ S' := fun h => (hmem v h).1 rfl
    refine ⟨insert v S', Finset.insert_subset hv (hS'U.trans hsub.subset), ?_, ?_⟩
    · intro x hx y hy hxy
      rcases Finset.mem_insert.1 hx with rfl | hx' <;> rcases Finset.mem_insert.1 hy with rfl | hy'
      · exact absurd rfl hxy
      · exact (hmem y hy').2
      · exact fun h => (hmem x hx').2 (hsymm _ _ h)
      · exact hS'ind x hx' y hy' hxy
    · have hcov : U ⊆ insert v (U.filter (r v) ∪ U') := by
        intro w hw
        by_cases hwv : w = v
        · simp [hwv]
        · by_cases hr : r v w
          · simp [hw, hr]
          · simp [hU', hw, hwv, hr]
      have h1 := Finset.card_le_card hcov
      have h2 := Finset.card_insert_le v (U.filter (r v) ∪ U')
      have h3 := Finset.card_union_le (U.filter (r v)) U'
      have h4 := hU v hv
      rw [Finset.card_insert_of_notMem hvS']
      nlinarith

/-- If a finite set `W` has no `blue` triangle and no `m`-subset that is pairwise non-`blue`,
then `|W| ≤ m(m-1)`. -/
theorem two_colour_bound {V : Type*} [DecidableEq V] (blue : V → V → Prop) [DecidableRel blue]
    (hsymm : ∀ x y, blue x y → blue y x) (m : ℕ) (W : Finset V)
    (htri : ∀ x ∈ W, ∀ y ∈ W, ∀ z ∈ W, blue x y → blue y z → blue x z → False)
    (hind : ∀ S ⊆ W, S.card = m → ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ ¬ ¬ blue x y) :
    W.card ≤ m * (m - 1) := by
  -- small subsets that are pairwise non-blue have size < m
  have hsmall : ∀ S ⊆ W, (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ blue x y) → S.card ≤ m - 1 := by
    intro S hSW hS
    by_contra h
    obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq (show m ≤ S.card by omega)
    obtain ⟨x, hx, y, hy, hxy, hb⟩ := hind T (hTS.trans hSW) hTc
    exact hb (hS x (hTS hx) y (hTS hy) hxy)
  have hm : 1 ≤ m := by
    by_contra h
    have h0 : m = 0 := by omega
    obtain ⟨x, hx, _⟩ := hind ∅ (Finset.empty_subset _) (by simp [h0])
    simp at hx
  have hdeg : ∀ v ∈ W, (W.filter (blue v)).card ≤ m - 1 := by
    intro v hv
    apply hsmall _ (Finset.filter_subset _ _)
    intro x hx y hy _ hxy
    simp only [Finset.mem_filter] at hx hy
    exact htri v hv x hx.1 y hy.1 hx.2 hxy hy.2
  obtain ⟨S, hSW, hSind, hcard⟩ := greedy blue hsymm (m - 1) W hdeg
  have := hsmall S hSW hSind
  have hm' : m - 1 + 1 = m := by omega
  rw [hm'] at hcard
  calc W.card ≤ m * S.card := hcard
    _ ≤ m * (m - 1) := Nat.mul_le_mul_left _ this

lemma fin2_eq_one {c : Fin 2} (h : c ≠ 0) : c = 1 := by
  fin_cases c <;> simp_all

lemma triangle_clique {N r : ℕ} (c : Sym2 (Fin N) → Fin r) (i : Fin r) (x y z : Fin N)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h1 : c s(x, y) = i) (h2 : c s(y, z) = i) (h3 : c s(x, z) = i) : MonoClique c i 3 := by
  refine ⟨{x, y, z}, Finset.card_eq_three.2 ⟨x, y, z, hxy, hxz, hyz, rfl⟩, ?_⟩
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hab
    | assumption
    | (rwa [Sym2.eq_swap])

/-- `R(3,m) ≤ m(m-1)+1`. -/
theorem good3 (m : ℕ) : Good3 m (m * (m - 1) + 1) := by
  intro c
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, h1⟩ := hcon
  let blue : Fin (m * (m - 1) + 1) → Fin (m * (m - 1) + 1) → Prop := fun x y => x ≠ y ∧ c s(x, y) = 0
  have hsymm : ∀ x y, blue x y → blue y x := fun x y h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩
  have hb := two_colour_bound blue hsymm m Finset.univ
    (fun x _ y _ z _ hxy hyz hxz => h0 (triangle_clique c 0 x y z hxy.1 hxz.1 hyz.1 hxy.2 hyz.2 hxz.2))
    (by
      intro S _ hS
      by_contra hne
      push Not at hne
      apply h1
      refine ⟨S, hS, fun x hx y hy hxy => fin2_eq_one ?_⟩
      intro hc
      exact hne x hx y hy hxy ⟨hxy, hc⟩)
  simp at hb

/-- `R(3,3,m) ≤ (2m(m-1)+1)(m-1)+1`. -/
theorem good33' (m N : ℕ) (hN : N = (2 * (m * (m - 1)) + 1) * (m - 1) + 1) : Good33 m N := by
  intro c
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, h1, h2⟩ := hcon
  have hcol : ∀ x y : Fin N, c s(x, y) ≠ 0 → c s(x, y) ≠ 1 → c s(x, y) = 2 := by
    intro x y a b
    generalize c s(x, y) = e at a b ⊢
    fin_cases e <;> simp_all
  -- the neighbourhood of `v` in colour `i ∈ {0,1}` has at most `m(m-1)` vertices
  have hnbhd : ∀ (i j : Fin 3), (i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0) → ∀ v : Fin N,
      (Finset.univ.filter (fun u => u ≠ v ∧ c s(v, u) = i)).card ≤ m * (m - 1) := by
    intro i j hij v
    let blue : Fin N → Fin N → Prop := fun x y => x ≠ y ∧ c s(x, y) = j
    have hsymm : ∀ x y, blue x y → blue y x :=
      fun x y h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩
    have hnoi : ∀ x ∈ Finset.univ.filter (fun u => u ≠ v ∧ c s(v, u) = i),
        ∀ y ∈ Finset.univ.filter (fun u => u ≠ v ∧ c s(v, u) = i), x ≠ y → c s(x, y) ≠ i := by
      intro x hx y hy hxy hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h0 (triangle_clique c 0 v x y hx.1.symm hy.1.symm hxy hx.2 hc hy.2)
      · exact h1 (triangle_clique c 1 v x y hx.1.symm hy.1.symm hxy hx.2 hc hy.2)
    apply two_colour_bound blue hsymm m _
    · intro x _ y _ z _ hxy hyz hxz
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h1 (triangle_clique c 1 x y z hxy.1 hxz.1 hyz.1 hxy.2 hyz.2 hxz.2)
      · exact h0 (triangle_clique c 0 x y z hxy.1 hxz.1 hyz.1 hxy.2 hyz.2 hxz.2)
    · intro S hSW hS
      by_contra hne
      push Not at hne
      apply h2
      refine ⟨S, hS, fun x hx y hy hxy => ?_⟩
      have hxi := hnoi x (hSW hx) y (hSW hy) hxy
      have hxj : c s(x, y) ≠ j := fun hc => hne x hx y hy hxy ⟨hxy, hc⟩
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcol x y hxi hxj
      · exact hcol x y hxj hxi
  let r01 : Fin N → Fin N → Prop := fun x y => x ≠ y ∧ (c s(x, y) = 0 ∨ c s(x, y) = 1)
  have hsymm : ∀ x y, r01 x y → r01 y x :=
    fun x y h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩
  have hdeg : ∀ v ∈ (Finset.univ : Finset (Fin N)),
      ((Finset.univ : Finset (Fin N)).filter (r01 v)).card ≤ 2 * (m * (m - 1)) := by
    intro v _
    have hsub : (Finset.univ : Finset (Fin N)).filter (r01 v) ⊆
        Finset.univ.filter (fun u => u ≠ v ∧ c s(v, u) = 0) ∪
          Finset.univ.filter (fun u => u ≠ v ∧ c s(v, u) = 1) := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, r01] at hu
      rcases hu.2 with h | h
      · simp [hu.1.symm, h]
      · simp [hu.1.symm, h]
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have a := hnbhd 0 1 (Or.inl ⟨rfl, rfl⟩) v
    have b := hnbhd 1 0 (Or.inr ⟨rfl, rfl⟩) v
    omega
  obtain ⟨S, -, hSind, hcard⟩ := greedy r01 hsymm _ Finset.univ hdeg
  have hS : S.card ≤ m - 1 := by
    by_contra h
    obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq (show m ≤ S.card by omega)
    apply h2
    refine ⟨T, hTc, fun x hx y hy hxy => ?_⟩
    have := hSind x (hTS hx) y (hTS hy) hxy
    simp only [r01, not_and, not_or] at this
    exact hcol x y (this hxy).1 (this hxy).2
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  have := Nat.mul_le_mul_left (2 * (m * (m - 1)) + 1) hS
  subst hN
  omega

theorem good33 (m : ℕ) : Good33 m ((2 * (m * (m - 1)) + 1) * (m - 1) + 1) := good33' m _ rfl

end JSP444


open Finset

namespace JSP444

/-- `(-1)^z` for `z : ZMod 2`. -/
def sgn (z : ZMod 2) : ℤ := if z = 0 then 1 else -1

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_eq_of_add {a b : ZMod 2} (h : a + b = 0) : a = b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    first | rfl | exact absurd h (by decide)

lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

@[simp] lemma sgn_zero : sgn 0 = 1 := by decide
@[simp] lemma sgn_one : sgn 1 = -1 := by decide
@[simp] lemma abs_sgn (a : ZMod 2) : |sgn a| = 1 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

/-- A nontrivial `±1` character sums to zero. -/
lemma sum_sgn_eq_zero {A : Type*} [AddCommGroup A] [Fintype A] (ψ : A →+ ZMod 2) (a1 : A)
    (h : ψ a1 = 1) : ∑ x, sgn (ψ x) = 0 := by
  have e : ∑ x, sgn (ψ (x + a1)) = ∑ x, sgn (ψ x) :=
    Fintype.sum_equiv (Equiv.addRight a1) _ _ (fun x => rfl)
  simp only [map_add, h, sgn_add, sgn_one, mul_neg_one, Finset.sum_neg_distrib] at e
  linarith

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

lemma self_add_F (x : F) : x + x = 0 := CharTwo.add_self_eq_zero x

lemma self_add_V (u : Fin 3 → F) : u + u = 0 := funext fun i => self_add_F (u i)

lemma add_eq_zero_V {v w : Fin 3 → F} (h : v + w = 0) : w = v := by
  funext i
  have h' := congrFun h i
  simp only [Pi.add_apply, Pi.zero_apply] at h'
  calc w i = (v i + w i) + v i := by rw [add_comm (v i) (w i), add_assoc, self_add_F, add_zero]
    _ = v i := by rw [h', zero_add]

variable (φ : F →+ ZMod 2)

/-- The trace-one-like set `T = φ⁻¹(1)`. -/
def T : Finset F := univ.filter (fun x => φ x = 1)

lemma ne_zero_of_mem_T {x : F} (hx : x ∈ T φ) : x ≠ 0 := by
  rintro rfl
  simp [T] at hx

lemma card_T_two (x1 : F) (hx1 : φ x1 = 1) : 2 * (T φ).card = Fintype.card F := by
  have h := sum_sgn_eq_zero φ x1 hx1
  have hsum : ∑ x, sgn (φ x) = ∑ x, (if φ x = 0 then (1 : ℤ) else -1) := rfl
  rw [hsum, Finset.sum_ite] at h
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg] at h
  have hc := Finset.card_filter_add_card_filter_not (s := (univ : Finset F))
    (fun x => φ x = 0)
  have hT : (univ.filter (fun x => ¬ φ x = 0)) = T φ := by
    ext x
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases zmod2_cases (φ x) with h | h <;> simp [h]
  rw [hT] at h hc
  rw [Finset.card_univ] at hc
  omega

lemma exists_split (x1 : F) (hx1 : φ x1 = 1) (z : F) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    ∃ x0, φ x0 = 0 ∧ φ (x0 * z) = 1 := by
  by_contra hcon
  push Not at hcon
  have hker : ∀ x, φ x = 0 → φ (x * z) = 0 := by
    intro x hx
    rcases zmod2_cases (φ (x * z)) with h | h
    · exact h
    · exact absurd h (hcon x hx)
  have hlin : ∀ x, φ (x * z) = φ x * φ (x1 * z) := by
    intro x
    rcases zmod2_cases (φ x) with h | h
    · rw [hker x h, h, zero_mul]
    · have h2 : φ (x + x1) = 0 := by rw [map_add, h, hx1]; decide
      have h3 := hker _ h2
      rw [add_mul, map_add] at h3
      rw [h, one_mul]
      exact zmod2_eq_of_add h3
  set c := φ (x1 * z)
  rcases zmod2_cases c with hc | hc
  · -- `φ(x z) = 0` for all `x`
    have hw : φ (x1 * z⁻¹ * z) = 0 := by rw [hlin, hc, mul_zero]
    rw [mul_assoc, inv_mul_cancel₀ hz0, mul_one, hx1] at hw
    exact one_ne_zero hw
  · have hw : ∀ x, φ (x * (z + 1)) = 0 := by
      intro x
      rw [mul_add, mul_one, map_add, hlin, hc, mul_one]
      rcases zmod2_cases (φ x) with h | h <;> rw [h] <;> decide
    have hz' : z + 1 ≠ 0 := by
      intro h
      apply hz1
      calc z = z + 1 + 1 := by rw [add_assoc, self_add_F, add_zero]
        _ = 1 := by rw [h, zero_add]
    have := hw (x1 * (z + 1)⁻¹)
    rw [mul_assoc, inv_mul_cancel₀ hz', mul_one, hx1] at this
    exact one_ne_zero this

lemma inner_sum (x1 : F) (hx1 : φ x1 = 1) (z : F) :
    |∑ x ∈ T φ, sgn (φ (x * z))| ≤ if z = 0 ∨ z = 1 then ((T φ).card : ℤ) else 0 := by
  split_ifs with hz
  · calc |∑ x ∈ T φ, sgn (φ (x * z))| ≤ ∑ x ∈ T φ, |sgn (φ (x * z))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = (T φ).card := by simp
  · push Not at hz
    obtain ⟨x0, h0, h1⟩ := exists_split φ x1 hx1 z hz.1 hz.2
    have hmem : ∀ a ∈ T φ, a + x0 ∈ T φ := by
      intro a ha
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [map_add, ha, h0, add_zero]
    have hinv : ∀ a, a + x0 + x0 = a := fun a => by rw [add_assoc, self_add_F, add_zero]
    have key : ∑ x ∈ T φ, sgn (φ (x * z)) = ∑ x ∈ T φ, -sgn (φ (x * z)) :=
      Finset.sum_nbij' (· + x0) (· + x0) hmem hmem (fun a _ => hinv a) (fun a _ => hinv a)
        (fun a _ => by rw [add_mul, map_add, h1, sgn_add, sgn_one]; ring)
    rw [Finset.sum_neg_distrib] at key
    have : ∑ x ∈ T φ, sgn (φ (x * z)) = 0 := by linarith
    rw [this, abs_zero]

/-! ### Characters of `F³` -/

/-- The character `v ↦ (-1)^{φ(a·v)}`. -/
def chi (a v : Fin 3 → F) : ℤ := sgn (φ (dotProduct a v))

lemma chi_add (a u v : Fin 3 → F) : chi φ a (u + v) = chi φ a u * chi φ a v := by
  simp [chi, dotProduct_add, map_add, sgn_add]

@[simp] lemma chi_zero_left (v : Fin 3 → F) : chi φ 0 v = 1 := by simp [chi]

lemma sum_chi (x1 : F) (hx1 : φ x1 = 1) (u : Fin 3 → F) :
    ∑ a, chi φ a u = if u = 0 then (Fintype.card (Fin 3 → F) : ℤ) else 0 := by
  split_ifs with hu
  · subst hu
    simp [chi]
  · obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h
      push Not at h
      exact hu (funext h)
    let ψ : (Fin 3 → F) →+ ZMod 2 :=
      { toFun := fun a => φ (dotProduct a u)
        map_zero' := by simp
        map_add' := by intro a b; simp [add_dotProduct] }
    apply sum_sgn_eq_zero ψ (Pi.single i (x1 * (u i)⁻¹))
    simp only [ψ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [single_dotProduct, mul_assoc, inv_mul_cancel₀ hi, mul_one, hx1]

lemma parseval (x1 : F) (hx1 : φ x1 = 1) (h : (Fin 3 → F) → ℤ) :
    ∑ a, (∑ v, h v * chi φ a v) ^ 2 = (Fintype.card (Fin 3 → F) : ℤ) * ∑ v, h v ^ 2 := by
  have key : ∀ a, (∑ v, h v * chi φ a v) ^ 2 = ∑ v, ∑ w, h v * h w * chi φ a (v + w) := by
    intro a
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun w _ => ?_))
    rw [chi_add]
    ring
  simp_rw [key]
  calc ∑ a, ∑ v, ∑ w, h v * h w * chi φ a (v + w)
      = ∑ v, ∑ w, h v * h w * ∑ a, chi φ a (v + w) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ v, h v * h v * (Fintype.card (Fin 3 → F) : ℤ) := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [Finset.sum_eq_single v]
        · rw [sum_chi φ x1 hx1, if_pos (self_add_V v)]
        · intro w _ hwv
          rw [sum_chi φ x1 hx1, if_neg, mul_zero]
          intro h0
          exact hwv (add_eq_zero_V h0)
        · simp
    _ = (Fintype.card (Fin 3 → F) : ℤ) * ∑ v, h v ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun v _ => ?_)
        ring

/-! ### The graph -/

/-- `(x, y) ↦ x · (y, y², y³)`. -/
def wv (p : F × F) : Fin 3 → F := ![p.1 * p.2, p.1 * p.2 ^ 2, p.1 * p.2 ^ 3]

/-- The generating set `S = { x (y, y², y³) : φ x = 1, y ≠ 0 }`. -/
def S : Finset (Fin 3 → F) := ((T φ) ×ˢ (univ.erase (0 : F))).image wv

lemma wv_injOn : Set.InjOn (wv (F := F)) ((T φ) ×ˢ (univ.erase (0 : F)) : Finset (F × F)) := by
  rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_erase,
    Finset.mem_univ, and_true] at hp hp'
  have hx := ne_zero_of_mem_T φ hp.1
  have hx' := ne_zero_of_mem_T φ hp'.1
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [wv, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hy : y = y' := by
    have e : (x * y) * y = (x' * y') * y' := by linear_combination h1
    rw [h0] at e
    exact mul_left_cancel₀ (mul_ne_zero hx' hp'.2) e
  subst hy
  have : x = x' := mul_right_cancel₀ hp.2 h0
  rw [this]

lemma zero_not_mem_S : (0 : Fin 3 → F) ∉ S φ := by
  intro h
  simp only [S, Finset.mem_image, Finset.mem_product, Finset.mem_erase, Finset.mem_univ,
    and_true] at h
  obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, he⟩ := h
  have h0 := congrFun he 0
  simp only [wv, Matrix.cons_val_zero, Pi.zero_apply] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · exact ne_zero_of_mem_T φ hx h
  · exact hy h

lemma card_S : (S φ).card = (T φ).card * (Fintype.card F - 1) := by
  rw [S, Finset.card_image_of_injOn (wv_injOn φ), Finset.card_product,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

/-- No three generators sum to zero. -/
lemma no_zero_sum (s1 s2 s3 : Fin 3 → F) (h1 : s1 ∈ S φ) (h2 : s2 ∈ S φ) (h3 : s3 ∈ S φ) :
    s1 + s2 + s3 ≠ 0 := by
  simp only [S, Finset.mem_image, Finset.mem_product, Finset.mem_erase, Finset.mem_univ,
    and_true] at h1 h2 h3
  obtain ⟨⟨x1, y1⟩, ⟨hx1, hy1⟩, rfl⟩ := h1
  obtain ⟨⟨x2, y2⟩, ⟨hx2, hy2⟩, rfl⟩ := h2
  obtain ⟨⟨x3, y3⟩, ⟨hx3, hy3⟩, rfl⟩ := h3
  simp only at hx1 hy1 hx2 hy2 hx3 hy3
  intro h
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  simp only [wv, Pi.add_apply, Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2
  have nx1 := ne_zero_of_mem_T φ hx1
  have nx2 := ne_zero_of_mem_T φ hx2
  have nx3 := ne_zero_of_mem_T φ hx3
  have k1 : x1 * y1 * ((y1 - y2) * (y1 - y3)) = 0 := by
    linear_combination e2 - (y2 + y3) * e1 + y2 * y3 * e0
  have k2 : x2 * y2 * ((y2 - y1) * (y2 - y3)) = 0 := by
    linear_combination e2 - (y1 + y3) * e1 + y1 * y3 * e0
  have k3 : x3 * y3 * ((y3 - y1) * (y3 - y2)) = 0 := by
    linear_combination e2 - (y1 + y2) * e1 + y1 * y2 * e0
  have c1 : y1 = y2 ∨ y1 = y3 := by
    rcases mul_eq_zero.1 k1 with h | h
    · exact absurd h (mul_ne_zero nx1 hy1)
    · rcases mul_eq_zero.1 h with h | h
      · exact Or.inl (sub_eq_zero.1 h)
      · exact Or.inr (sub_eq_zero.1 h)
  have c2 : y2 = y1 ∨ y2 = y3 := by
    rcases mul_eq_zero.1 k2 with h | h
    · exact absurd h (mul_ne_zero nx2 hy2)
    · rcases mul_eq_zero.1 h with h | h
      · exact Or.inl (sub_eq_zero.1 h)
      · exact Or.inr (sub_eq_zero.1 h)
  have c3 : y3 = y1 ∨ y3 = y2 := by
    rcases mul_eq_zero.1 k3 with h | h
    · exact absurd h (mul_ne_zero nx3 hy3)
    · rcases mul_eq_zero.1 h with h | h
      · exact Or.inl (sub_eq_zero.1 h)
      · exact Or.inr (sub_eq_zero.1 h)
  have hall : y2 = y1 ∧ y3 = y1 := by
    rcases c1 with h | h
    · rcases c3 with h' | h'
      · exact ⟨h.symm, h'⟩
      · exact ⟨h.symm, h'.trans h.symm⟩
    · rcases c2 with h' | h'
      · exact ⟨h', h.symm⟩
      · exact ⟨h'.trans h.symm, h.symm⟩
  rw [hall.1, hall.2] at e0
  have hs : (x1 + x2 + x3) * y1 = 0 := by linear_combination e0
  have hs' : x1 + x2 + x3 = 0 := (mul_eq_zero.1 hs).resolve_right hy1
  have := congrArg φ hs'
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2 hx3
  rw [map_add, map_add, hx1, hx2, hx3, map_zero] at this
  exact absurd this (by decide)

/-- The Cayley graph of `F³` with generating set `S`. -/
def G : SimpleGraph (Fin 3 → F) where
  Adj u v := u + v ∈ S φ
  symm := ⟨fun u v (h : u + v ∈ S φ) => by rwa [add_comm]⟩
  loopless := ⟨fun u (h : u + u ∈ S φ) => zero_not_mem_S φ (by rwa [self_add_V] at h)⟩

instance : DecidableRel (G φ).Adj := fun u v => inferInstanceAs (Decidable (u + v ∈ S φ))

lemma G_cliqueFree : (G φ).CliqueFree 3 := by
  intro t ht
  rw [SimpleGraph.is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
  apply no_zero_sum φ _ _ _ hab hbc hac
  have : a + b + (b + c) + (a + c) = (a + a) + (b + b) + (c + c) := by abel
  rw [this]
  simp only [self_add_V, add_zero]

/-! ### Eigenvalues -/

lemma roots_le (a : Fin 3 → F) (ha : a ≠ 0) (c : F) :
    (univ.filter (fun y : F => a 0 * y + a 1 * y ^ 2 + a 2 * y ^ 3 = c)).card ≤ 3 := by
  set Q : Polynomial F := Polynomial.C (a 0) * Polynomial.X + Polynomial.C (a 1) * Polynomial.X ^ 2
    + Polynomial.C (a 2) * Polynomial.X ^ 3 - Polynomial.C c with hQdef
  have hQ : Q ≠ 0 := by
    intro hQ
    have h1 := congrArg (fun p => Polynomial.coeff p 1) hQ
    have h2 := congrArg (fun p => Polynomial.coeff p 2) hQ
    have h3 := congrArg (fun p => Polynomial.coeff p 3) hQ
    simp [Q, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow] at h1 h2 h3
    apply ha
    funext i
    fin_cases i <;> simp [h1, h2, h3]
  have hdeg : Q.natDegree ≤ 3 := by
    rw [hQdef]
    compute_degree
  calc (univ.filter (fun y : F => a 0 * y + a 1 * y ^ 2 + a 2 * y ^ 3 = c)).card
      ≤ Q.roots.toFinset.card := by
        apply Finset.card_le_card
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ]
        simp [Q, hy]
    _ ≤ Multiset.card Q.roots := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := Polynomial.card_roots' Q
    _ ≤ 3 := hdeg

lemma lam_bound (x1 : F) (hx1 : φ x1 = 1) (a : Fin 3 → F) (ha : a ≠ 0) :
    |∑ s ∈ S φ, chi φ a s| ≤ 6 * ((T φ).card : ℤ) := by
  set P : F → F := fun y => a 0 * y + a 1 * y ^ 2 + a 2 * y ^ 3 with hP
  have hpt : ∀ p : F × F, chi φ a (wv p) = sgn (φ (p.1 * P p.2)) := by
    rintro ⟨x, y⟩
    simp only [chi, wv, hP]
    congr 2
    simp [dotProduct, Fin.sum_univ_three]
    ring
  rw [S, Finset.sum_image (wv_injOn φ)]
  simp_rw [hpt]
  rw [Finset.sum_product_right]
  calc |∑ y ∈ univ.erase (0 : F), ∑ x ∈ T φ, sgn (φ (x * P y))|
      ≤ ∑ y ∈ univ.erase (0 : F), |∑ x ∈ T φ, sgn (φ (x * P y))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ univ.erase (0 : F), (if P y = 0 ∨ P y = 1 then ((T φ).card : ℤ) else 0) :=
        Finset.sum_le_sum (fun y _ => inner_sum φ x1 hx1 (P y))
    _ = ((univ.erase (0 : F)).filter (fun y => P y = 0 ∨ P y = 1)).card * ((T φ).card : ℤ) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 6 * ((T φ).card : ℤ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hsub : (univ.erase (0 : F)).filter (fun y => P y = 0 ∨ P y = 1) ⊆
            univ.filter (fun y => P y = 0) ∪ univ.filter (fun y => P y = 1) := by
          intro y hy
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hy
          rcases hy.2 with h | h <;> simp [h]
        have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have r0 := roots_le a ha 0
        have r1 := roots_le a ha 1
        simp only [hP] at this ⊢
        exact_mod_cast (show _ ≤ 6 by omega)

/-! ### Spectral bound on `B` -/

/-- Number of neighbours of `v` inside `B`, written as a convolution. -/
def gB (B : Finset (Fin 3 → F)) (v : Fin 3 → F) : ℤ :=
  ∑ s ∈ S φ, if v + s ∈ B then 1 else 0

def fB (B : Finset (Fin 3 → F)) (v : Fin 3 → F) : ℤ := if v ∈ B then 1 else 0

lemma gB_eq_card (B : Finset (Fin 3 → F)) (v : Fin 3 → F) :
    gB φ B v = ((B.filter ((G φ).Adj v)).card : ℤ) := by
  rw [gB, Finset.sum_boole]
  congr 1
  apply Finset.card_nbij' (v + ·) (v + ·)
  · intro s hs
    simp only [Finset.mem_coe, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter] at hs ⊢
    refine ⟨hs.2, ?_⟩
    show v + (v + s) ∈ S φ
    rw [← add_assoc, self_add_V, zero_add]
    exact hs.1
  · intro b hb
    simp only [Finset.mem_coe, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter] at hb ⊢
    have hb2 : v + b ∈ S φ := hb.2
    refine ⟨hb2, ?_⟩
    rw [← add_assoc, self_add_V, zero_add]
    exact hb.1
  · intro s _
    simp only
    rw [← add_assoc, self_add_V, zero_add]
  · intro b _
    simp only
    rw [← add_assoc, self_add_V, zero_add]

lemma hat_gB (B : Finset (Fin 3 → F)) (a : Fin 3 → F) :
    ∑ v, gB φ B v * chi φ a v = (∑ s ∈ S φ, chi φ a s) * ∑ v, fB B v * chi φ a v := by
  simp only [gB, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have e : ∑ w, (if w + s + s ∈ B then (1 : ℤ) else 0) * chi φ a (w + s) =
      ∑ v, (if v + s ∈ B then (1 : ℤ) else 0) * chi φ a v :=
    Fintype.sum_equiv (Equiv.addRight s) _ _ (fun w => rfl)
  rw [← e, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [add_assoc, self_add_V, add_zero, chi_add, fB]
  ring

lemma sum_fB_sq (B : Finset (Fin 3 → F)) : ∑ v, fB B v ^ 2 = B.card := by
  have : ∀ v, fB B v ^ 2 = fB B v := fun v => by unfold fB; split_ifs <;> simp
  simp_rw [this, fB, Finset.sum_boole]
  simp [Finset.filter_mem_eq_inter]

lemma sum_fB (B : Finset (Fin 3 → F)) : ∑ v, fB B v = B.card := by
  simp only [fB, Finset.sum_boole]
  simp [Finset.filter_mem_eq_inter]

/-- `n Σ_v g(v)² ≤ d²|B|² + Λ² n |B|` with `Λ = 6|T|`. -/
theorem spectral (x1 : F) (hx1 : φ x1 = 1) (B : Finset (Fin 3 → F)) :
    (Fintype.card (Fin 3 → F) : ℤ) * ∑ v, gB φ B v ^ 2 ≤
      ((S φ).card : ℤ) ^ 2 * (B.card : ℤ) ^ 2 +
        (6 * (T φ).card : ℤ) ^ 2 * (Fintype.card (Fin 3 → F) : ℤ) * B.card := by
  rw [← parseval φ x1 hx1]
  simp_rw [hat_gB, mul_pow]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin 3 → F))]
  have h0 : (∑ s ∈ S φ, chi φ 0 s) = (S φ).card := by simp
  have h0' : ∑ v, fB B v * chi φ 0 v = B.card := by simp [sum_fB]
  rw [h0, h0']
  have hrest : ∑ a ∈ univ.erase (0 : Fin 3 → F),
      (∑ s ∈ S φ, chi φ a s) ^ 2 * (∑ v, fB B v * chi φ a v) ^ 2 ≤
      (6 * (T φ).card : ℤ) ^ 2 * (Fintype.card (Fin 3 → F) : ℤ) * B.card := by
    calc ∑ a ∈ univ.erase (0 : Fin 3 → F),
          (∑ s ∈ S φ, chi φ a s) ^ 2 * (∑ v, fB B v * chi φ a v) ^ 2
        ≤ ∑ a ∈ univ.erase (0 : Fin 3 → F),
          (6 * (T φ).card : ℤ) ^ 2 * (∑ v, fB B v * chi φ a v) ^ 2 := by
          apply Finset.sum_le_sum
          intro a ha
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          have := lam_bound φ x1 hx1 a (Finset.ne_of_mem_erase ha)
          exact sq_le_sq' (by linarith [abs_le.1 this]) (abs_le.1 this).2
      _ ≤ ∑ a, (6 * (T φ).card : ℤ) ^ 2 * (∑ v, fB B v * chi φ a v) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun _ _ _ => by positivity)
      _ = (6 * (T φ).card : ℤ) ^ 2 * (Fintype.card (Fin 3 → F) : ℤ) * B.card := by
          rw [← Finset.mul_sum, parseval φ x1 hx1, sum_fB_sq]
          ring
  linarith

end JSP444


open Finset

namespace JSP444

section Count

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Independent `m`-subsets of `B`. -/
def indSets (m : ℕ) (B : Finset V) : Finset (Finset V) :=
  (B.powersetCard m).filter (fun S => ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y)

/-- Vertices of `B` other than `v` that are not adjacent to `v`. -/
def rest (B : Finset V) (v : V) : Finset V := (B.erase v).filter (fun w => ¬ G.Adj v w)

lemma card_ind_succ (m : ℕ) (B : Finset V) :
    (m + 1) * (indSets G (m + 1) B).card ≤ ∑ v ∈ B, (indSets G m (rest G B v)).card := by
  have hsum : (m + 1) * (indSets G (m + 1) B).card =
      ∑ v ∈ B, ((indSets G (m + 1) B).filter (fun S => v ∈ S)).card := by
    have h1 : ∀ S ∈ indSets G (m + 1) B, S.card = ∑ v ∈ B, if v ∈ S then 1 else 0 := by
      intro S hS
      simp only [indSets, Finset.mem_filter, Finset.mem_powersetCard] at hS
      rw [Finset.sum_boole, Nat.cast_id]
      congr 1
      ext x
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨hS.1.1 h, h⟩, fun h => h.2⟩
    calc (m + 1) * (indSets G (m + 1) B).card
        = ∑ S ∈ indSets G (m + 1) B, S.card := by
          rw [Finset.sum_const_nat (s := indSets G (m + 1) B) (m := m + 1)
            (fun S hS => (Finset.mem_powersetCard.1 (Finset.mem_filter.1 hS).1).2), mul_comm]
      _ = ∑ S ∈ indSets G (m + 1) B, ∑ v ∈ B, if v ∈ S then 1 else 0 :=
          Finset.sum_congr rfl h1
      _ = ∑ v ∈ B, ∑ S ∈ indSets G (m + 1) B, if v ∈ S then 1 else 0 := Finset.sum_comm
      _ = ∑ v ∈ B, ((indSets G (m + 1) B).filter (fun S => v ∈ S)).card := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.sum_boole, Nat.cast_id]
  rw [hsum]
  apply Finset.sum_le_sum
  intro v _
  apply Finset.card_le_card_of_injOn (fun S => S.erase v)
  · intro S hS
    simp only [Finset.coe_filter, Set.mem_setOf_eq, indSets, Finset.mem_filter,
      Finset.mem_powersetCard] at hS
    simp only [Finset.mem_coe, indSets, rest, Finset.mem_filter, Finset.mem_powersetCard]
    obtain ⟨⟨⟨hSB, hScard⟩, hind⟩, hv⟩ := hS
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro w hw
      rw [Finset.mem_erase] at hw
      simp only [Finset.mem_filter, Finset.mem_erase]
      exact ⟨⟨hw.1, hSB hw.2⟩, hind v hv w hw.2⟩
    · rw [Finset.card_erase_of_mem hv, hScard]
      rfl
    · intro x hx y hy
      exact hind x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)
  · intro S hS S' hS' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hS hS'
    simp only at h
    rw [← Finset.insert_erase hS.2, ← Finset.insert_erase hS'.2, h]

lemma card_ind_one (B : Finset V) : (indSets G 1 B).card = B.card := by
  have : indSets G 1 B = B.powersetCard 1 := by
    apply Finset.filter_true_of_mem
    intro S hS x hx y hy
    rw [Finset.mem_powersetCard, Finset.card_eq_one] at hS
    obtain ⟨a, rfl⟩ := hS.2
    rw [Finset.mem_singleton] at hx hy
    subst hx; subst hy
    exact G.loopless.irrefl _
  rw [this, Finset.card_powersetCard, Nat.choose_one_right]

/-- Kleitman–Winston style bound on independent sets. -/
theorem kw (R δ : ℝ) (t : ℕ) (hR : 1 / 2 ≤ R) (ht : 1 ≤ t) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hn : (Fintype.card V : ℝ) * (1 - δ) ^ t ≤ R)
    (hC : ∀ B : Finset V,
      ((B.filter (fun v => ((B.filter (G.Adj v)).card : ℝ) ≤ δ * B.card)).card : ℝ) ≤ R) :
    ∀ m : ℕ, ∀ B : Finset V,
      ((m + 1).factorial * (indSets G (m + 1) B).card : ℝ) ≤ (2 * R) ^ (m + 1) * (B.card : ℝ) ^ t := by
  intro m
  induction m with
  | zero =>
    intro B
    rw [card_ind_one]
    simp only [zero_add, Nat.factorial_one, Nat.cast_one, one_mul, pow_one]
    have h1 : (B.card : ℝ) ≤ (B.card : ℝ) ^ t := by
      rcases Nat.eq_zero_or_pos B.card with h | h
      · simp [h]
      · exact le_self_pow₀ (by exact_mod_cast h) (by omega)
    have h2 : 0 ≤ (B.card : ℝ) ^ t := by positivity
    nlinarith
  | succ m ih =>
    intro B
    have hcard := card_ind_succ G (m + 1) B
    have hR0 : 0 ≤ 2 * R := by linarith
    -- per-vertex bound
    have hv : ∀ v ∈ B, ((m + 1).factorial * (indSets G (m + 1) (rest G B v)).card : ℝ) ≤
        (2 * R) ^ (m + 1) * ((rest G B v).card : ℝ) ^ t := fun v _ => ih _
    -- size of `rest`
    have hrest : ∀ v ∈ B, ((rest G B v).card : ℝ) + (B.filter (G.Adj v)).card ≤ B.card := by
      intro v _
      have hdisj : Disjoint (rest G B v) (B.filter (G.Adj v)) := by
        rw [Finset.disjoint_left]
        intro w hw hw'
        simp only [rest, Finset.mem_filter] at hw hw'
        exact hw.2 hw'.2
      have hsub : rest G B v ∪ B.filter (G.Adj v) ⊆ B := by
        intro w hw
        rcases Finset.mem_union.1 hw with h | h
        · exact Finset.mem_of_mem_erase (Finset.mem_filter.1 h).1
        · exact (Finset.mem_filter.1 h).1
      have := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj] at this
      exact_mod_cast this
    set low := B.filter (fun v => ((B.filter (G.Adj v)).card : ℝ) ≤ δ * B.card) with hlow
    set X : V → ℝ := fun v => (2 * R) ^ (m + 1) * ((rest G B v).card : ℝ) ^ t with hX
    have hlowX : ∀ v ∈ low, X v ≤ (2 * R) ^ (m + 1) * (B.card : ℝ) ^ t := by
      intro v hv'
      have hvB := (Finset.mem_filter.1 hv').1
      have := hrest v hvB
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hR0 _)
      apply pow_le_pow_left₀ (by positivity)
      linarith [(Finset.card_filter_le B (G.Adj v) : _), (show (0 : ℝ) ≤ (B.filter (G.Adj v)).card by positivity)]
    have hhighX : ∀ v ∈ B.filter (fun v => ¬ (((B.filter (G.Adj v)).card : ℝ) ≤ δ * B.card)),
        X v ≤ (2 * R) ^ (m + 1) * ((1 - δ) ^ t * (B.card : ℝ) ^ t) := by
      intro v hv'
      obtain ⟨hvB, hbig⟩ := Finset.mem_filter.1 hv'
      have := hrest v hvB
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hR0 _)
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      push Not at hbig
      nlinarith
    calc ((m + 1 + 1).factorial * (indSets G (m + 1 + 1) B).card : ℝ)
        = (m + 1).factorial * ((m + 1 + 1) * (indSets G (m + 1 + 1) B).card : ℕ) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
      _ ≤ (m + 1).factorial * (∑ v ∈ B, (indSets G (m + 1) (rest G B v)).card : ℕ) := by
          gcongr
      _ = ∑ v ∈ B, ((m + 1).factorial * (indSets G (m + 1) (rest G B v)).card : ℝ) := by
          push_cast
          rw [Finset.mul_sum]
      _ ≤ ∑ v ∈ B, X v := Finset.sum_le_sum hv
      _ = ∑ v ∈ low, X v + ∑ v ∈ B.filter (fun v => ¬ (((B.filter (G.Adj v)).card : ℝ) ≤ δ * B.card)), X v :=
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      _ ≤ ∑ v ∈ low, (2 * R) ^ (m + 1) * (B.card : ℝ) ^ t +
          ∑ v ∈ B.filter (fun v => ¬ (((B.filter (G.Adj v)).card : ℝ) ≤ δ * B.card)),
            (2 * R) ^ (m + 1) * ((1 - δ) ^ t * (B.card : ℝ) ^ t) :=
          add_le_add (Finset.sum_le_sum hlowX) (Finset.sum_le_sum hhighX)
      _ ≤ R * ((2 * R) ^ (m + 1) * (B.card : ℝ) ^ t) +
          (Fintype.card V : ℝ) * ((2 * R) ^ (m + 1) * ((1 - δ) ^ t * (B.card : ℝ) ^ t)) := by
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
          have hP : 0 ≤ (2 * R) ^ (m + 1) * (B.card : ℝ) ^ t := by positivity
          have hP' : 0 ≤ (2 * R) ^ (m + 1) * ((1 - δ) ^ t * (B.card : ℝ) ^ t) := by
            have : 0 ≤ 1 - δ := by linarith
            positivity
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right (hC B) hP
          · apply mul_le_mul_of_nonneg_right _ hP'
            exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_le_univ _)
      _ ≤ (2 * R) ^ (m + 1 + 1) * (B.card : ℝ) ^ t := by
          have hP : 0 ≤ (2 * R) ^ (m + 1) * (B.card : ℝ) ^ t := by positivity
          have : (Fintype.card V : ℝ) * ((2 * R) ^ (m + 1) * ((1 - δ) ^ t * (B.card : ℝ) ^ t)) =
              ((Fintype.card V : ℝ) * (1 - δ) ^ t) * ((2 * R) ^ (m + 1) * (B.card : ℝ) ^ t) := by ring
          rw [this]
          have h1 := mul_le_mul_of_nonneg_right hn hP
          have e : (2 * R) ^ (m + 1 + 1) * (B.card : ℝ) ^ t =
              2 * R * ((2 * R) ^ (m + 1) * (B.card : ℝ) ^ t) := by ring
          rw [e]
          linarith

end Count

section Perm

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma exists_perm_map (S' S'' : Finset V) (h : S'.card = S''.card) :
    ∃ τ : Equiv.Perm V, S'.map τ.toEmbedding = S'' := by
  have e1 : {x // x ∈ S'} ≃ {x // x ∈ S''} :=
    Fintype.equivOfCardEq (by simp [h])
  have e2 : {x // x ∉ S'} ≃ {x // x ∉ S''} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]; simp [h])
  refine ⟨Equiv.subtypeCongr e1 e2, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' : (Equiv.subtypeCongr e1 e2) x = e1 ⟨x, hx⟩ := by simp [Equiv.subtypeCongr, hx]
    rw [Equiv.toEmbedding_apply, hx']
    exact (e1 ⟨x, hx⟩).2
  · rw [Finset.card_map, h]

/-- If `|I|² < C(n,m)` for a family `I` of `m`-sets, some permutation moves every member of `I`
outside `I`. -/
theorem exists_perm_avoid (m : ℕ) (I : Finset (Finset V)) (hI : ∀ S ∈ I, S.card = m)
    (h : I.card ^ 2 < (Fintype.card V).choose m) :
    ∃ σ : Equiv.Perm V, ∀ S ∈ I, S.map σ.toEmbedding ∉ I := by
  classical
  let c : Finset V → Finset V → ℕ := fun S S' =>
    ((Finset.univ : Finset (Equiv.Perm V)).filter (fun σ => S.map σ.toEmbedding = S')).card
  -- `c S S'` does not depend on `S'`
  have hconst : ∀ S S' S'', S'.card = S''.card → c S S' = c S S'' := by
    intro S S' S'' hcard
    obtain ⟨τ, hτ⟩ := exists_perm_map S' S'' hcard
    have hτ' : S''.map τ⁻¹.toEmbedding = S' := by
      rw [← hτ, Finset.map_map]
      convert Finset.map_refl
      ext x
      simp
    apply Finset.card_nbij' (τ * ·) (τ⁻¹ * ·)
    · intro σ hσ
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hσ ⊢
      rw [← hτ, ← hσ, Finset.map_map]
      rfl
    · intro σ hσ
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hσ ⊢
      rw [← hτ', ← hσ, Finset.map_map]
      rfl
    · intro σ _
      simp
    · intro σ _
      simp
  -- summing `c S ·` over all `m`-sets gives `n!`
  have htotal : ∀ S : Finset V, S.card = m →
      ∑ S' ∈ (Finset.univ : Finset V).powersetCard m, c S S' = (Fintype.card V).factorial := by
    intro S hS
    rw [← Fintype.card_perm, ← Finset.card_univ]
    symm
    apply Finset.card_eq_sum_card_fiberwise
    intro σ _
    simp [Finset.mem_powersetCard, hS]
  have hm : m ≤ Fintype.card V := by
    by_contra hm
    push Not at hm
    rw [Nat.choose_eq_zero_of_lt hm] at h
    omega
  obtain ⟨S0, hS0⟩ : ∃ S0 : Finset V, S0.card = m :=
    Finset.exists_subset_card_eq (s := Finset.univ) (by simpa using hm) |>.imp fun _ h => h.2
  set c0 := c S0 S0 with hc0
  have hceq : ∀ S S', S.card = m → S'.card = m → c S S' = c0 := by
    intro S S' hS hS'
    rw [hconst S S' S (by rw [hS, hS'])]
    obtain ⟨τ, hτ⟩ := exists_perm_map S0 S (by rw [hS0, hS])
    -- `c S S = c S0 S0` via conjugation
    have hτ' : S.map τ⁻¹.toEmbedding = S0 := by
      rw [← hτ, Finset.map_map]
      convert Finset.map_refl
      ext x
      simp
    have : c S S = c S0 S0 := by
      apply Finset.card_nbij' (fun σ => τ⁻¹ * σ * τ) (fun σ => τ * σ * τ⁻¹)
      · intro σ hσ
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hσ ⊢
        calc S0.map (τ⁻¹ * σ * τ).toEmbedding
            = (S.map τ⁻¹.toEmbedding).map (τ⁻¹ * σ * τ).toEmbedding := by rw [hτ']
          _ = (S.map σ.toEmbedding).map τ⁻¹.toEmbedding := by
              rw [Finset.map_map, Finset.map_map]
              congr 1
              ext x
              simp [Equiv.Perm.mul_apply]
          _ = S0 := by rw [hσ, hτ']
      · intro σ hσ
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hσ ⊢
        calc S.map (τ * σ * τ⁻¹).toEmbedding
            = (S0.map τ.toEmbedding).map (τ * σ * τ⁻¹).toEmbedding := by rw [hτ]
          _ = (S0.map σ.toEmbedding).map τ.toEmbedding := by
              rw [Finset.map_map, Finset.map_map]
              congr 1
              ext x
              simp [Equiv.Perm.mul_apply]
          _ = S := by rw [hσ, hτ]
      · intro σ _
        simp [mul_assoc]
      · intro σ _
        simp [mul_assoc]
    exact this
  have hfact : (Fintype.card V).choose m * c0 = (Fintype.card V).factorial := by
    rw [← htotal S0 hS0, Finset.sum_congr rfl (fun S' hS' => hceq S0 S' hS0
      (Finset.mem_powersetCard.1 hS').2), Finset.sum_const, Finset.card_powersetCard,
      Finset.card_univ, smul_eq_mul]
  by_contra hcon
  push Not at hcon
  -- every permutation has at least one bad pair
  have hge : (Fintype.card V).factorial ≤
      ∑ σ : Equiv.Perm V, (I.filter (fun S => S.map σ.toEmbedding ∈ I)).card := by
    rw [← Fintype.card_perm, ← Finset.card_univ, Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro σ _
    obtain ⟨S, hS, hS'⟩ := hcon σ
    exact Finset.card_pos.2 ⟨S, Finset.mem_filter.2 ⟨hS, hS'⟩⟩
  have hsum : ∑ σ : Equiv.Perm V, (I.filter (fun S => S.map σ.toEmbedding ∈ I)).card =
      I.card * I.card * c0 := by
    have h1 : ∀ σ : Equiv.Perm V, (I.filter (fun S => S.map σ.toEmbedding ∈ I)).card =
        ∑ S ∈ I, if S.map σ.toEmbedding ∈ I then 1 else 0 := by
      intro σ
      rw [Finset.sum_boole, Nat.cast_id]
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ S ∈ I, (∑ σ : Equiv.Perm V, if S.map σ.toEmbedding ∈ I then 1 else 0) =
        I.card * c0 := by
      intro S hS
      rw [Finset.sum_boole, Nat.cast_id]
      have hfib := Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (Equiv.Perm V)).filter (fun σ => S.map σ.toEmbedding ∈ I))
        (t := I) (f := fun σ : Equiv.Perm V => S.map σ.toEmbedding)
        (by
          intro σ hσ
          simp only [Finset.mem_coe, Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq,
            Finset.mem_univ, true_and] at hσ ⊢
          exact hσ)
      rw [hfib]
      rw [Finset.sum_congr rfl (fun S' hS' => ?_), Finset.sum_const, smul_eq_mul]
      rw [← hceq S S' (hI S hS) (hI S' hS'), Finset.filter_filter]
      congr 1
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, h⟩
        exact h
      · rintro h
        exact ⟨h ▸ hS', h⟩
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul]
    ring
  have hc0pos : 0 < c0 := by
    rcases Nat.eq_zero_or_pos c0 with h0 | h0
    · rw [h0, mul_zero] at hfact
      exact absurd hfact.symm (Nat.factorial_ne_zero _)
    · exact h0
  rw [hsum, ← hfact] at hge
  have : I.card * I.card < (Fintype.card V).choose m := by rw [← sq]; exact h
  have := Nat.mul_lt_mul_of_pos_right this hc0pos
  omega

end Perm

end JSP444


/-! ## Part D: assembly -/

namespace JSP444

open Finset Filter Topology

/-! ### Elementary facts about the colourings -/

lemma monoClique_mono {N r : ℕ} (c : Sym2 (Fin N) → Fin r) (i : Fin r) {k k' : ℕ} (hk : k ≤ k')
    (h : MonoClique c i k') : MonoClique c i k := by
  obtain ⟨s, hs, hc⟩ := h
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show k ≤ s.card by omega)
  exact ⟨t, htc, fun x hx y hy hxy => hc x (hts hx) y (hts hy) hxy⟩

/-- A bad colouring of `K_N` restricts to a bad colouring of `K_{N'}` for `N' ≤ N`. -/
lemma not_good33_of_le {N N' M : ℕ} (hN : N' ≤ N) (c : Sym2 (Fin N) → Fin 3)
    (h0 : ¬ MonoClique c 0 3) (h1 : ¬ MonoClique c 1 3) (h2 : ¬ MonoClique c 2 M) :
    ¬ Good33 M N' := by
  intro hgood
  let f : Fin N' ↪ Fin N := Fin.castLEEmb hN
  have key : ∀ (i : Fin 3) (k : ℕ), MonoClique (c ∘ Sym2.map f) i k → MonoClique c i k := by
    rintro i k ⟨s, hs, hc⟩
    refine ⟨s.map f, by rw [Finset.card_map, hs], ?_⟩
    intro x hx y hy hxy
    rw [Finset.mem_map] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hne : x' ≠ y' := fun h => hxy (by rw [h])
    have := hc x' hx' y' hy' hne
    simpa [Function.comp, Sym2.map_mk] using this
  rcases hgood (c ∘ Sym2.map f) with h | h | h
  · exact h0 (key 0 3 h)
  · exact h1 (key 1 3 h)
  · exact h2 (key 2 M h)

lemma lt_R33 {N M : ℕ} (c : Sym2 (Fin N) → Fin 3)
    (h0 : ¬ MonoClique c 0 3) (h1 : ¬ MonoClique c 1 3) (h2 : ¬ MonoClique c 2 M) :
    N < R33 M := by
  have hmem : Good33 M (R33 M) := by
    have := Nat.sInf_mem (s := {N | Good33 M N}) ⟨_, good33 M⟩
    exact this
  by_contra hle
  push Not at hle
  exact not_good33_of_le hle c h0 h1 h2 hmem

lemma R33_le (m : ℕ) : R33 m ≤ (2 * (m * (m - 1)) + 1) * (m - 1) + 1 := Nat.sInf_le (good33 m)

lemma R3_le (m : ℕ) : R3 m ≤ m * (m - 1) + 1 := Nat.sInf_le (good3 m)

lemma R3_pos {m : ℕ} (hm : 1 ≤ m) : 0 < R3 m := by
  have hmem : Good3 m (R3 m) := by
    have := Nat.sInf_mem (s := {N | Good3 m N}) ⟨_, good3 m⟩
    exact this
  rcases Nat.eq_zero_or_pos (R3 m) with h | h
  · exfalso
    rw [h] at hmem
    rcases hmem (fun _ => 0) with ⟨s, hs, _⟩ | ⟨s, hs, _⟩
    · have := s.card_le_univ
      rw [Fintype.card_fin] at this
      omega
    · have := s.card_le_univ
      rw [Fintype.card_fin] at this
      omega
  · exact h

/-! ### The lower-bound construction -/

section Lower

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (φ : F →+ ZMod 2)

/-- Few vertices of `B` have few neighbours in `B` (Alon–Rödl, Lemma 2.2). -/
theorem lowdeg (x1 : F) (hx1 : φ x1 = 1) (hdpos : 0 < (S φ).card) (B : Finset (Fin 3 → F)) :
    ((B.filter (fun v => (((B.filter ((G φ).Adj v)).card : ℝ) ≤
        (((S φ).card : ℝ) / (2 * (Fintype.card (Fin 3 → F) : ℝ))) * (B.card : ℝ)))).card : ℝ) ≤
      2 * (6 * ((T φ).card : ℝ)) * (Fintype.card (Fin 3 → F) : ℝ) / ((S φ).card : ℝ) := by
  set g : (Fin 3 → F) → ℝ := fun v => ((B.filter ((G φ).Adj v)).card : ℝ) with hg
  set n : ℝ := (Fintype.card (Fin 3 → F) : ℝ) with hn
  set d : ℝ := ((S φ).card : ℝ) with hd
  set L : ℝ := 6 * ((T φ).card : ℝ) with hL
  set b : ℝ := (B.card : ℝ) with hb
  set C := B.filter (fun v => g v ≤ (d / (2 * n)) * b) with hC
  have hnpos : 0 < n := by
    rw [hn]
    exact_mod_cast Fintype.card_pos
  have hdpos' : 0 < d := by rw [hd]; exact_mod_cast hdpos
  have hb0 : 0 ≤ b := by positivity
  have hgB : ∀ v, g v = (gB φ B v : ℝ) := fun v => by simp [hg, gB_eq_card]
  have hspec : n * ∑ v, g v ^ 2 ≤ d ^ 2 * b ^ 2 + L ^ 2 * n * b := by
    have h := spectral φ x1 hx1 B
    simp_rw [hgB]
    rw [hn, hd, hL, hb]
    exact_mod_cast h
  have hsum : ∑ v, g v = d * b := by
    have h := hat_gB φ B 0
    simp only [chi_zero_left, mul_one, Finset.sum_const, nsmul_eq_mul, sum_fB] at h
    simp_rw [hgB]
    rw [hd, hb]
    exact_mod_cast h
  have hsq : ∑ v, g v ^ 2 ≤ d ^ 2 * b ^ 2 / n + L ^ 2 * b := by
    rw [div_add' _ _ _ hnpos.ne', le_div_iff₀ hnpos]
    linarith
  have hvar : ∑ v, (g v - d * b / n) ^ 2 ≤ L ^ 2 * b := by
    have e : ∑ v, (g v - d * b / n) ^ 2 =
        ∑ v, g v ^ 2 - 2 * (d * b / n) * ∑ v, g v + n * (d * b / n) ^ 2 := by
      rw [Finset.sum_congr rfl (fun v _ => (by ring : (g v - d * b / n) ^ 2 =
        g v ^ 2 - 2 * (d * b / n) * g v + (d * b / n) ^ 2))]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    rw [e, hsum]
    have : - 2 * (d * b / n) * (d * b) + n * (d * b / n) ^ 2 = - (d ^ 2 * b ^ 2 / n) := by
      field_simp
      ring
    linarith
  have hCsum : (C.card : ℝ) * (d * b / (2 * n)) ^ 2 ≤ L ^ 2 * b := by
    calc (C.card : ℝ) * (d * b / (2 * n)) ^ 2 = ∑ v ∈ C, (d * b / (2 * n)) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ v ∈ C, (g v - d * b / n) ^ 2 := by
          apply Finset.sum_le_sum
          intro v hv
          have hv' : g v ≤ d / (2 * n) * b := (Finset.mem_filter.1 hv).2
          have h0 : 0 ≤ d * b / (2 * n) := by positivity
          have h2 : d * b / n = 2 * (d * b / (2 * n)) := by field_simp
          have h3 : d / (2 * n) * b = d * b / (2 * n) := by ring
          have h4 : d * b / (2 * n) ≤ d * b / n - g v := by linarith
          nlinarith
      _ ≤ ∑ v, (g v - d * b / n) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => sq_nonneg _)
      _ ≤ L ^ 2 * b := hvar
  have hCB : (C.card : ℝ) ≤ b := by
    rw [hb]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hC0 : (0 : ℝ) ≤ C.card := by positivity
  have hL0 : 0 ≤ L := by positivity
  rw [le_div_iff₀ hdpos']
  rcases eq_or_lt_of_le hb0 with hb' | hb'
  · rw [← hb'] at hCB
    have : (C.card : ℝ) = 0 := le_antisymm hCB hC0
    rw [this, zero_mul]
    positivity
  · -- `|C| d² b ≤ 4 L² n²`
    have e : (C.card : ℝ) * (d * b / (2 * n)) ^ 2 = (C.card * d ^ 2 * b) * b / (4 * n ^ 2) := by
      field_simp
      ring
    rw [e, div_le_iff₀ (by positivity)] at hCsum
    have h1 : (C.card : ℝ) * d ^ 2 * b ≤ 4 * L ^ 2 * n ^ 2 := by
      have : (C.card * d ^ 2 * b) * b ≤ (4 * L ^ 2 * n ^ 2) * b := by nlinarith
      exact le_of_mul_le_mul_right this hb'
    have h2 : ((C.card : ℝ) * d) ^ 2 ≤ (2 * L * n) ^ 2 := by
      have : (C.card : ℝ) * C.card * d ^ 2 ≤ C.card * b * d ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left hCB hC0
      nlinarith
    by_contra hcon
    push Not at hcon
    have h0 : 0 ≤ 2 * L * n := by positivity
    nlinarith

lemma two_pow_bound (k : ℕ) (hk : 12 ≤ k) : 2 ^ 15 * k ^ 2 ≤ 4 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : (k + 1) ^ 2 ≤ 4 * k ^ 2 := by nlinarith
    calc 2 ^ 15 * (k + 1) ^ 2 ≤ 4 * (2 ^ 15 * k ^ 2) := by nlinarith
      _ ≤ 4 * 4 ^ k := by omega
      _ = 4 ^ (k + 1) := by ring

/-- For `F` of size `q = 2^k` (`k ≥ 12`) there is a 3-colouring of `K_{q³}` with no triangle in
colours 0 and 1 and no `K_M` in colour 2, where `M = q · 2^14 · k²`. -/
theorem bad_colouring (k : ℕ) (hk : 12 ≤ k) (hq : Fintype.card F = 2 ^ k) (x1 : F)
    (hx1 : φ x1 = 1) :
    ∃ c : Sym2 (Fin (Fintype.card (Fin 3 → F))) → Fin 3,
      ¬ MonoClique c 0 3 ∧ ¬ MonoClique c 1 3 ∧ ¬ MonoClique c 2 (2 ^ k * 2 ^ 14 * k ^ 2) := by
  obtain ⟨q, hqdef⟩ : ∃ q, q = 2 ^ k := ⟨_, rfl⟩
  rw [← hqdef] at hq
  obtain ⟨M, hM⟩ : ∃ M, M = q * 2 ^ 14 * k ^ 2 := ⟨_, rfl⟩
  rw [show 2 ^ k * 2 ^ 14 * k ^ 2 = M by rw [hM, hqdef]]
  obtain ⟨t, ht⟩ : ∃ t, t = 24 * q * k := ⟨_, rfl⟩
  have hk0 : 0 < k := by omega
  have hq2 : 2 ≤ q := by
    rw [hqdef]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hn : Fintype.card (Fin 3 → F) = q ^ 3 := by
    rw [Fintype.card_fun, hq, Fintype.card_fin]
  have hT2 : 2 * (T φ).card = q := by rw [card_T_two φ x1 hx1, hq]
  have hS : (S φ).card = (T φ).card * (q - 1) := by rw [card_S, hq]
  -- real parameters
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hTR : ((T φ).card : ℝ) = q / 2 := by
    have : (2 * (T φ).card : ℝ) = q := by exact_mod_cast hT2
    linarith
  have hdR : ((S φ).card : ℝ) = q / 2 * (q - 1) := by
    rw [hS]
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)]
    rw [hTR]
  have hnR : (Fintype.card (Fin 3 → F) : ℝ) = (q : ℝ) ^ 3 := by rw [hn]; push_cast; ring
  have hdpos : 0 < (S φ).card := by
    rw [hS]
    apply Nat.mul_pos
    · omega
    · omega
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ((S φ).card : ℝ) / (2 * (Fintype.card (Fin 3 → F) : ℝ)) :=
    ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 24 * (q : ℝ) ^ 2 := ⟨_, rfl⟩
  have hδval : δ = (q - 1) / (4 * q ^ 2) := by
    rw [hδ, hdR, hnR]
    field_simp
    ring
  have hδ0 : 0 ≤ δ := by rw [hδval]; apply div_nonneg <;> nlinarith
  have hδ1 : δ ≤ 1 := by
    rw [hδval, div_le_one (show (0 : ℝ) < 4 * (q : ℝ) ^ 2 by positivity)]
    nlinarith
  -- the low-degree count is at most `R`
  have hC : ∀ B : Finset (Fin 3 → F),
      ((B.filter (fun v => (((B.filter ((G φ).Adj v)).card : ℝ) ≤ δ * B.card))).card : ℝ) ≤ R := by
    intro B
    rw [hδ]
    refine (lowdeg φ x1 hx1 hdpos B).trans ?_
    rw [hTR, hnR, hdR, hR, div_le_iff₀ (by nlinarith)]
    nlinarith
  -- `n (1-δ)^t ≤ R`
  have hnt : (Fintype.card (Fin 3 → F) : ℝ) * (1 - δ) ^ t ≤ R := by
    have h1 : (1 - δ) ^ t ≤ Real.exp (-(3 * k)) := by
      calc (1 - δ) ^ t ≤ Real.exp (-δ) ^ t :=
            pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-δ)]) t
        _ = Real.exp (-δ * t) := by rw [← Real.exp_nat_mul]; ring_nf
        _ ≤ Real.exp (-(3 * k)) := by
            apply Real.exp_le_exp.2
            have hdt : (3 * k : ℝ) ≤ δ * t := by
              rw [hδval, ht]
              push_cast
              have hq0 : (0 : ℝ) < q := by linarith
              rw [show ((q : ℝ) - 1) / (4 * (q : ℝ) ^ 2) * (24 * (q : ℝ) * k) =
                6 * k * ((q : ℝ) - 1) / q by field_simp; ring]
              rw [le_div_iff₀ hq0]
              have hk0' : (0 : ℝ) ≤ k := by positivity
              nlinarith
            linarith
    have h2 : Real.exp (-(3 * k)) * (q : ℝ) ^ 3 ≤ 1 := by
      have e3 : (8 : ℝ) ≤ Real.exp 3 := by
        have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have h : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        rw [h]
        calc (8 : ℝ) = 2 ^ 3 := by norm_num
          _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
      have hq3 : (q : ℝ) ^ 3 = (8 : ℝ) ^ k := by
        rw [hqdef]
        push_cast
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      rw [hq3, Real.exp_neg, ← div_eq_inv_mul, div_le_one (Real.exp_pos _)]
      have : Real.exp (3 * k) = Real.exp 3 ^ k := by rw [← Real.exp_nat_mul]; ring_nf
      rw [this]
      exact pow_le_pow_left₀ (by norm_num) e3 k
    rw [hnR]
    have hR1 : (1 : ℝ) ≤ R := by rw [hR]; nlinarith
    nlinarith [Real.exp_pos (-(3 * (k : ℝ))), pow_nonneg (show (0 : ℝ) ≤ 1 - δ by linarith) t]
  -- Kleitman–Winston count
  have hM1 : 1 ≤ M := by
    rw [hM]
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by norm_num)) (pow_pos hk0 2)
  have ht1 : 1 ≤ t := by
    rw [ht]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) hk0
  have hkw := kw (G φ) R δ t (by rw [hR]; nlinarith) ht1 hδ0 hδ1 hnt hC
    (M - 1) Finset.univ
  rw [Nat.sub_add_cancel hM1, Finset.card_univ] at hkw
  set I := indSets (G φ) M Finset.univ with hI
  -- `|I|² < C(n, M)`
  have h2M : 2 * M ≤ q ^ 3 := by
    have := two_pow_bound k hk
    have hq4 : q ^ 2 = 4 ^ k := by rw [hqdef, ← pow_mul, mul_comm, pow_mul]; norm_num
    calc 2 * M = q * (2 ^ 15 * k ^ 2) := by rw [hM]; ring
      _ ≤ q * 4 ^ k := Nat.mul_le_mul_left _ this
      _ = q ^ 3 := by rw [← hq4]; ring
  have hIsq : I.card ^ 2 < (Fintype.card (Fin 3 → F)).choose M := by
    by_contra hcon
    push Not at hcon
    -- binomial lower bound
    have hchoose := Nat.pow_le_choose (α := ℝ) M (Fintype.card (Fin 3 → F))
    have hsub : ((q : ℝ) ^ 3) / 2 ≤ ((Fintype.card (Fin 3 → F) + 1 - M : ℕ) : ℝ) := by
      rw [hn]
      have : M ≤ q ^ 3 + 1 := by omega
      push_cast [Nat.cast_sub this]
      have : (2 * M : ℝ) ≤ q ^ 3 := by exact_mod_cast h2M
      linarith
    have hfact : ((M : ℝ) / 3) ^ M ≤ M.factorial := by
      have h := Real.pow_div_factorial_le_exp (x := (M : ℝ)) (by positivity) M
      have he : Real.exp M ≤ 3 ^ M := by
        have : Real.exp M = Real.exp 1 ^ M := by rw [← Real.exp_nat_mul]; ring_nf
        rw [this]
        exact pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) M
      rw [div_pow, div_le_iff₀ (show (0 : ℝ) < 3 ^ M by positivity)]
      rw [div_le_iff₀ (show (0 : ℝ) < (M.factorial : ℝ) by positivity)] at h
      calc (M : ℝ) ^ M ≤ Real.exp M * M.factorial := h
        _ ≤ 3 ^ M * M.factorial := mul_le_mul_of_nonneg_right he (by positivity)
        _ = M.factorial * 3 ^ M := by ring
    have hFpos : (0 : ℝ) < M.factorial := by exact_mod_cast Nat.factorial_pos M
    have hcR : ((Fintype.card (Fin 3 → F)).choose M : ℝ) ≤ (I.card : ℝ) ^ 2 := by
      exact_mod_cast hcon
    -- `(n/2)^M (M/3)^M ≤ (2R)^(2M) n^(2t)`
    have hmain : ((q : ℝ) ^ 3 / 2) ^ M * ((M : ℝ) / 3) ^ M ≤
        ((2 * R) ^ M * ((q : ℝ) ^ 3) ^ t) ^ 2 := by
      have hA : ((q : ℝ) ^ 3 / 2) ^ M ≤ ((Fintype.card (Fin 3 → F)).choose M : ℝ) * M.factorial := by
        rw [div_le_iff₀ hFpos] at hchoose
        calc ((q : ℝ) ^ 3 / 2) ^ M ≤ (((Fintype.card (Fin 3 → F) + 1 - M : ℕ) : ℝ)) ^ M :=
              pow_le_pow_left₀ (by positivity) hsub M
          _ ≤ _ := hchoose
      have hB : (M.factorial : ℝ) * I.card ≤ (2 * R) ^ M * ((q : ℝ) ^ 3) ^ t := by
        rw [← hnR]
        exact hkw
      calc ((q : ℝ) ^ 3 / 2) ^ M * ((M : ℝ) / 3) ^ M
          ≤ ((Fintype.card (Fin 3 → F)).choose M : ℝ) * M.factorial * M.factorial := by
            apply mul_le_mul hA hfact (by positivity) (by positivity)
        _ ≤ (I.card : ℝ) ^ 2 * M.factorial * M.factorial := by
            gcongr
        _ = ((M.factorial : ℝ) * I.card) ^ 2 := by ring
        _ ≤ ((2 * R) ^ M * ((q : ℝ) ^ 3) ^ t) ^ 2 := by
            apply pow_le_pow_left₀ (by positivity) hB
    -- numerics: the left side is strictly larger
    have hnat : (q ^ 3) ^ (2 * t) < (k ^ 2) ^ M := by
      have hk4 : 4 ≤ k ^ 2 := by nlinarith
      have e1 : (q ^ 3) ^ (2 * t) = 2 ^ (6 * k * t) := by
        rw [hqdef, ← pow_mul, ← pow_mul]
        ring_nf
      have h1 : 6 * k * t < 2 * M := by
        rw [ht, hM]
        have : 0 < q * k ^ 2 := by positivity
        nlinarith
      calc (q ^ 3) ^ (2 * t) = 2 ^ (6 * k * t) := e1
        _ < 2 ^ (2 * M) := Nat.pow_lt_pow_right (by norm_num) h1
        _ = 4 ^ M := by rw [pow_mul]; norm_num
        _ ≤ (k ^ 2) ^ M := Nat.pow_le_pow_left hk4 M
    have hnatR : (((q : ℝ) ^ 3) ^ t) ^ 2 < ((k : ℝ) ^ 2) ^ M := by
      rw [← pow_mul, mul_comm t 2]
      exact_mod_cast hnat
    have hbase : (2 * R) ^ 2 * (k : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 / 2 * ((M : ℝ) / 3) := by
      rw [hR, hM]
      push_cast
      have e1 : (2 * (24 * (q : ℝ) ^ 2)) ^ 2 * (k : ℝ) ^ 2 = 2304 * ((q : ℝ) ^ 4 * (k : ℝ) ^ 2) := by
        ring
      have e2 : (q : ℝ) ^ 3 / 2 * ((q : ℝ) * 16384 * (k : ℝ) ^ 2 / 3) =
          (16384 / 6) * ((q : ℝ) ^ 4 * (k : ℝ) ^ 2) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    have hR0 : (0 : ℝ) < 2 * R := by rw [hR]; positivity
    have : ((2 * R) ^ M * ((q : ℝ) ^ 3) ^ t) ^ 2 < ((q : ℝ) ^ 3 / 2) ^ M * ((M : ℝ) / 3) ^ M := by
      calc ((2 * R) ^ M * ((q : ℝ) ^ 3) ^ t) ^ 2
          = ((2 * R) ^ 2) ^ M * (((q : ℝ) ^ 3) ^ t) ^ 2 := by
            have e : ((2 * R) ^ M) ^ 2 = ((2 * R) ^ 2) ^ M := pow_right_comm _ _ _
            rw [mul_pow, e]
        _ < ((2 * R) ^ 2) ^ M * ((k : ℝ) ^ 2) ^ M :=
            mul_lt_mul_of_pos_left hnatR (by positivity)
        _ = ((2 * R) ^ 2 * (k : ℝ) ^ 2) ^ M := (mul_pow _ _ M).symm
        _ ≤ ((q : ℝ) ^ 3 / 2 * ((M : ℝ) / 3)) ^ M := pow_le_pow_left₀ (by positivity) hbase M
        _ = ((q : ℝ) ^ 3 / 2) ^ M * ((M : ℝ) / 3) ^ M := mul_pow _ _ M
    linarith
  -- a permutation separating the independent sets
  have hIcard : ∀ S ∈ I, S.card = M := by
    intro S hS
    exact (Finset.mem_powersetCard.1 (Finset.mem_filter.1 hS).1).2
  obtain ⟨σ, hσ⟩ := exists_perm_avoid M I hIcard hIsq
  -- the colouring
  let V := Fin 3 → F
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let f : Fin (Fintype.card V) → Fin (Fintype.card V) → Fin 3 := fun i j =>
    if (G φ).Adj (e i) (e j) then 0 else if (G φ).Adj (σ (e i)) (σ (e j)) then 1 else 2
  have hf : ∀ i j, f i j = f j i := by
    intro i j
    simp only [f, (G φ).adj_comm (e i) (e j), (G φ).adj_comm (σ (e i)) (σ (e j))]
  let c : Sym2 (Fin (Fintype.card V)) → Fin 3 := Sym2.lift ⟨f, hf⟩
  have hc : ∀ i j, c s(i, j) = f i j := fun i j => by simp [c]
  have hf0 : ∀ i j, f i j = 0 → (G φ).Adj (e i) (e j) := by
    intro i j h
    by_contra hn
    simp only [f, hn, if_false] at h
    split_ifs at h <;> exact absurd h (by decide)
  have hf1 : ∀ i j, f i j = 1 → (G φ).Adj (σ (e i)) (σ (e j)) := by
    intro i j h
    by_contra hn
    simp only [f, hn, if_false] at h
    split_ifs at h <;> exact absurd h (by decide)
  have hf2 : ∀ i j, f i j = 2 → ¬ (G φ).Adj (e i) (e j) ∧ ¬ (G φ).Adj (σ (e i)) (σ (e j)) := by
    intro i j h
    by_cases h1 : (G φ).Adj (e i) (e j)
    · simp only [f, h1, if_true] at h
      exact absurd h (by decide)
    · by_cases h2 : (G φ).Adj (σ (e i)) (σ (e j))
      · simp only [f, h1, h2, if_true, if_false] at h
        exact absurd h (by decide)
      · exact ⟨h1, h2⟩
  refine ⟨c, ?_, ?_, ?_⟩
  · rintro ⟨s, hs, hcol⟩
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hs
    have a1 := hf0 _ _ ((hc x y).symm.trans (hcol x (by simp) y (by simp) hxy))
    have a2 := hf0 _ _ ((hc x z).symm.trans (hcol x (by simp) z (by simp) hxz))
    have a3 := hf0 _ _ ((hc y z).symm.trans (hcol y (by simp) z (by simp) hyz))
    exact G_cliqueFree φ _ (SimpleGraph.is3Clique_triple_iff.2 ⟨a1, a2, a3⟩)
  · rintro ⟨s, hs, hcol⟩
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hs
    have a1 := hf1 _ _ ((hc x y).symm.trans (hcol x (by simp) y (by simp) hxy))
    have a2 := hf1 _ _ ((hc x z).symm.trans (hcol x (by simp) z (by simp) hxz))
    have a3 := hf1 _ _ ((hc y z).symm.trans (hcol y (by simp) z (by simp) hyz))
    exact G_cliqueFree φ _ (SimpleGraph.is3Clique_triple_iff.2 ⟨a1, a2, a3⟩)
  · rintro ⟨s, hs, hcol⟩
    have hind : ∀ x ∈ s, ∀ y ∈ s, ¬ (G φ).Adj (e x) (e y) ∧ ¬ (G φ).Adj (σ (e x)) (σ (e y)) := by
      intro x hx y hy
      by_cases hxy : x = y
      · subst hxy
        exact ⟨(G φ).loopless.irrefl _, (G φ).loopless.irrefl _⟩
      · exact hf2 _ _ ((hc x y).symm.trans (hcol x hx y hy hxy))
    have hmem : s.map e.toEmbedding ∈ I := by
      simp only [hI, indSets, Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, by rw [Finset.card_map, hs]⟩, ?_⟩
      intro a ha b hb
      rw [Finset.mem_map] at ha hb
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      exact (hind x hx y hy).1
    apply hσ _ hmem
    simp only [hI, indSets, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, by rw [Finset.card_map, Finset.card_map, hs]⟩, ?_⟩
    intro a ha b hb
    rw [Finset.map_map, Finset.mem_map] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact (hind x hx y hy).2

end Lower

/-- Instantiation with `GaloisField 2 k`: `R(3,3,M) > 2^(3k)` for `M ≥ 2^k · 2^14 · k²`. -/
theorem R33_lower (k : ℕ) (hk : 12 ≤ k) (M : ℕ) (hM : 2 ^ k * 2 ^ 14 * k ^ 2 ≤ M) :
    (2 ^ k) ^ 3 < R33 M := by
  classical
  let F := GaloisField 2 k
  letI : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = 2 ^ k := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 k (by omega)
  obtain ⟨φ0, hφ0⟩ : ∃ φ0 : Module.Dual (ZMod 2) F, φ0 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) (1 : F)).1 h)
  have hφ1 : φ0 1 = 1 := (zmod2_cases _).resolve_left hφ0
  obtain ⟨c, h0, h1, h2⟩ := bad_colouring (F := F) φ0.toAddMonoidHom k hk hq 1 hφ1
  have hn : Fintype.card (Fin 3 → F) = (2 ^ k) ^ 3 := by
    rw [Fintype.card_fun, hq, Fintype.card_fin]
  rw [← hn]
  exact lt_R33 c h0 h1 (fun h => h2 (monoClique_mono c 2 hM h))

lemma sq_bound (m : ℕ) (hm : 1 ≤ m) : m * (m - 1) + 1 ≤ m ^ 2 := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  nlinarith

lemma cube_bound (m : ℕ) (hm : 1 ≤ m) : (2 * (m * (m - 1)) + 1) * (m - 1) + 1 ≤ 2 * m ^ 3 := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  nlinarith

/-! ### The main theorem -/

/-- **JSP-000444 / Erdős #553.** `R(3,3,m) = m³ (log m)^{O(1)}`: there are constants with
`c m³ / (log m)⁶ ≤ R(3,3,m) ≤ C m³` for all large `m` (Alon–Rödl); consequently
`R(3,3,m) / R(3,m) → ∞` (the Erdős–Sós conjecture). -/
theorem jsp_000444 :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ m : ℕ in atTop,
        c * (m : ℝ) ^ 3 / Real.log m ^ 6 ≤ R33 m ∧ (R33 m : ℝ) ≤ C * (m : ℝ) ^ 3) ∧
    Tendsto (fun m : ℕ => (R33 m : ℝ) / R3 m) atTop atTop := by
  set c : ℝ := 1 / 2 ^ 57 with hc
  have hc0 : 0 < c := by positivity
  set m0 : ℕ := 2 ^ 12 * 2 ^ 14 * 12 ^ 2 with hm0
  -- lower bound for all `m ≥ m0`
  have hlow : ∀ m : ℕ, m0 ≤ m → c * (m : ℝ) ^ 3 / Real.log m ^ 6 ≤ R33 m := by
    intro m hm
    let P : ℕ → Prop := fun k => 2 ^ k * 2 ^ 14 * k ^ 2 ≤ m
    have hP12 : P 12 := hm
    have h12m : 12 ≤ m := le_trans (show 12 ≤ m0 by rw [hm0]; norm_num) hm
    set k := Nat.findGreatest P m with hk
    have hk12 : 12 ≤ k := Nat.le_findGreatest h12m hP12
    have hPk : P k := Nat.findGreatest_spec h12m hP12
    have hnext : m < 2 ^ (k + 1) * 2 ^ 14 * (k + 1) ^ 2 := by
      by_contra hcon
      push Not at hcon
      have hk1 : k + 1 ≤ m := by
        have : k + 1 ≤ 2 ^ (k + 1) * 2 ^ 14 * (k + 1) ^ 2 := by
          have h1 : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
          have h2 : 1 ≤ 2 ^ 14 * (k + 1) ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
          calc k + 1 ≤ 2 ^ (k + 1) := h1.le
            _ = 2 ^ (k + 1) * 1 := by ring
            _ ≤ 2 ^ (k + 1) * (2 ^ 14 * (k + 1) ^ 2) := Nat.mul_le_mul_left _ h2
            _ = 2 ^ (k + 1) * 2 ^ 14 * (k + 1) ^ 2 := by ring
        omega
      exact Nat.findGreatest_is_greatest (Nat.lt_succ_self k) hk1 hcon
    have hR := R33_lower k hk12 m hPk
    have hRR : ((2 : ℝ) ^ k) ^ 3 ≤ R33 m := by exact_mod_cast hR.le
    refine le_trans ?_ hRR
    -- numerics
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have h2k : (2 : ℝ) ^ k ≤ m := by
      have : 2 ^ k ≤ m := le_trans (by
        calc 2 ^ k = 2 ^ k * 1 * 1 := by ring
          _ ≤ 2 ^ k * 2 ^ 14 * k ^ 2 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ Nat.one_le_two_pow)
              (Nat.one_le_pow _ _ (by omega))) hPk
      exact_mod_cast this
    have hlog : (k : ℝ) / 2 ≤ Real.log m := by
      have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log m := Real.log_le_log (by positivity) h2k
      rw [Real.log_pow] at h1
      have := Real.log_two_gt_d9
      nlinarith
    have hm3 : (m : ℝ) ^ 3 ≤ 2 ^ 51 * ((2 : ℝ) ^ k) ^ 3 * (k : ℝ) ^ 6 := by
      have hnext' : (m : ℝ) ≤ 2 ^ 17 * (2 : ℝ) ^ k * (k : ℝ) ^ 2 := by
        have : (m : ℝ) < 2 ^ (k + 1) * 2 ^ 14 * ((k : ℝ) + 1) ^ 2 := by exact_mod_cast hnext
        have hk12' : (12 : ℝ) ≤ k := by exact_mod_cast hk12
        have hk1 : ((k : ℝ) + 1) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by nlinarith
        have : (2 : ℝ) ^ (k + 1) * 2 ^ 14 * ((k : ℝ) + 1) ^ 2 ≤ 2 ^ 17 * (2 : ℝ) ^ k * (k : ℝ) ^ 2 := by
          rw [pow_succ]
          nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) k]
        linarith
      calc (m : ℝ) ^ 3 ≤ (2 ^ 17 * (2 : ℝ) ^ k * (k : ℝ) ^ 2) ^ 3 :=
            pow_le_pow_left₀ hmpos.le hnext' 3
        _ = 2 ^ 51 * ((2 : ℝ) ^ k) ^ 3 * (k : ℝ) ^ 6 := by ring
    have hlog6 : ((k : ℝ) / 2) ^ 6 ≤ Real.log m ^ 6 := pow_le_pow_left₀ (by positivity) hlog 6
    have hlogpos : 0 < Real.log m ^ 6 := lt_of_lt_of_le (by positivity) hlog6
    rw [div_le_iff₀ hlogpos]
    calc c * (m : ℝ) ^ 3 ≤ c * (2 ^ 51 * ((2 : ℝ) ^ k) ^ 3 * (k : ℝ) ^ 6) :=
          mul_le_mul_of_nonneg_left hm3 hc0.le
      _ = ((2 : ℝ) ^ k) ^ 3 * ((k : ℝ) / 2) ^ 6 := by rw [hc]; ring
      _ ≤ ((2 : ℝ) ^ k) ^ 3 * Real.log m ^ 6 := by gcongr
  -- upper bound
  have hup : ∀ m : ℕ, 1 ≤ m → (R33 m : ℝ) ≤ 2 * (m : ℝ) ^ 3 := by
    intro m hm
    have h' := (R33_le m).trans (cube_bound m hm)
    calc (R33 m : ℝ) ≤ ((2 * m ^ 3 : ℕ) : ℝ) := Nat.cast_le.2 h'
      _ = 2 * (m : ℝ) ^ 3 := by push_cast; ring
  refine ⟨⟨c, 2, hc0, by norm_num, ?_⟩, ?_⟩
  · filter_upwards [Filter.eventually_ge_atTop m0] with m hm
    exact ⟨hlow m hm, hup m (le_trans (Nat.one_le_iff_ne_zero.2 (show m0 ≠ 0 by rw [hm0]; positivity)) hm)⟩
  · -- `c m / (log m)^6 → ∞`
    have hlim : Tendsto (fun x : ℝ => x / Real.log x ^ 6) atTop atTop := by
      have h0 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 6 one_ne_zero
      simp only [one_mul, add_zero] at h0
      have hpos : ∀ᶠ x : ℝ in atTop, 0 < Real.log x ^ 6 / x := by
        filter_upwards [Filter.eventually_gt_atTop (Real.exp 1)] with x hx
        have hx1 : 1 < x := lt_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hx
        have : 0 < Real.log x := Real.log_pos hx1
        positivity
      have h1 := (tendsto_nhdsWithin_iff.2 ⟨h0, hpos⟩).inv_tendsto_nhdsGT_zero
      refine h1.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
      simp [inv_div]
    have hlimN : Tendsto (fun m : ℕ => c * ((m : ℝ) / Real.log m ^ 6)) atTop atTop :=
      (hlim.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc0
    refine tendsto_atTop_mono' atTop ?_ hlimN
    filter_upwards [Filter.eventually_ge_atTop m0] with m hm
    have hm1 : 1 ≤ m := le_trans (Nat.one_le_iff_ne_zero.2 (show m0 ≠ 0 by rw [hm0]; positivity)) hm
    have hR3pos : (0 : ℝ) < R3 m := by exact_mod_cast R3_pos hm1
    have hR3le : (R3 m : ℝ) ≤ (m : ℝ) ^ 2 := by
      have h := R3_le m
      have h' := h.trans (sq_bound m hm1)
      calc (R3 m : ℝ) ≤ ((m ^ 2 : ℕ) : ℝ) := Nat.cast_le.2 h'
        _ = (m : ℝ) ^ 2 := by push_cast; ring
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hl := hlow m hm
    rw [le_div_iff₀ hR3pos]
    calc c * ((m : ℝ) / Real.log m ^ 6) * R3 m ≤ c * ((m : ℝ) / Real.log m ^ 6) * (m : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left hR3le
          have : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm1)
          positivity
      _ = c * (m : ℝ) ^ 3 / Real.log m ^ 6 := by ring
      _ ≤ R33 m := hl

end JSP444


