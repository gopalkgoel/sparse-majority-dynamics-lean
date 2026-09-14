import MajorityDynamics.Local.CoarseData

/-! Literal LA1–LA9 from `def:local-admissibility`, with the original ties. -/
noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Local
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

/-- The common ordered-edge fluctuation scale. -/
def edgeScale (N : ℕ) (p : ℝ) : ℝ := (N : ℝ) ^ 2 * p / Real.sqrt (p * N)

/-- The local hypotheses used before the child-edge kernel step.  In
particular, history conditioning is retained but no lower bound is imposed on
the two new child probabilities.  This is the appropriate terminal notion. -/
structure CoreAdmissible (y : CoarseData V n) (q : Tilt n) (T φ p : ℝ) : Prop where
  regularity : y.reg = true
  sizes : ∀ s, T⁻¹ * (Fintype.card V : ℝ) ≤ (y.sizes s : ℝ)
  imbalances : ∀ r : Fin n,
    |∑ t, character r.castSucc t * (y.sizes t : ℝ)| ≤
      T * (Fintype.card V : ℝ) / Real.sqrt (p * Fintype.card V)
  edge_scale : ∀ s t, |y.realEdges s t - p * (y.sizes s : ℝ) * (y.sizes t : ℝ)| ≤
    T * edgeScale (Fintype.card V) p
  positive : ∀ s t, 0 < y.realEdges s t
  separation : ∀ s (r : Fin n),
    decision (bits (n + 1) s r.castSucc) (bits (n + 1) s r.succ)
      ((∑ t, character r.castSucc t * y.realEdges s t) -
        sign (bits (n + 1) s r.succ) * (T⁻¹ * edgeScale (Fintype.card V) p))
  tilt : ∀ s t, |(q s t : ℝ) - p| ≤
    T * p / Real.sqrt (p * Fintype.card V)
  conditioning : ∀ s, φ ≤ Binomial.eventMass (trials y.sizes s) (q s)
    (historySupport y.sizes s)
  solves : Solves y.sizes y.realEdges q

structure Admissible (y : CoarseData V n) (q : Tilt n) (T φ p : ℝ) : Prop where
  regularity : y.reg = true
  sizes : ∀ s, T⁻¹ * (Fintype.card V : ℝ) ≤ (y.sizes s : ℝ)
  imbalances : ∀ r : Fin n,
    |∑ t, character r.castSucc t * (y.sizes t : ℝ)| ≤
      T * (Fintype.card V : ℝ) / Real.sqrt (p * Fintype.card V)
  edge_scale : ∀ s t, |y.realEdges s t - p * (y.sizes s : ℝ) * (y.sizes t : ℝ)| ≤
    T * edgeScale (Fintype.card V) p
  positive : ∀ s t, 0 < y.realEdges s t
  separation : ∀ s (r : Fin n),
    decision (bits (n + 1) s r.castSucc) (bits (n + 1) s r.succ)
      ((∑ t, character r.castSucc t * y.realEdges s t) -
        sign (bits (n + 1) s r.succ) * (T⁻¹ * edgeScale (Fintype.card V) p))
  tilt : ∀ s t, |(q s t : ℝ) - p| ≤
    T * p / Real.sqrt (p * Fintype.card V)
  conditioning : ∀ s, φ ≤ Binomial.eventMass (trials y.sizes s) (q s)
    (historySupport y.sizes s)
  solves : Solves y.sizes y.realEdges q
  split : ∀ s b, φ ≤ splitProbability y.sizes q s b ∧
    splitProbability y.sizes q s b ≤ 1 - φ

theorem Admissible.toCore {y : CoarseData V n} {q : Tilt n} {T φ p : ℝ}
    (h : Admissible y q T φ p) : CoreAdmissible y q T φ p where
  regularity := h.regularity
  sizes := h.sizes
  imbalances := h.imbalances
  edge_scale := h.edge_scale
  positive := h.positive
  separation := h.separation
  tilt := h.tilt
  conditioning := h.conditioning
  solves := h.solves

theorem decision_margin_mono (a b : Bool) {x c d : ℝ} (hdc : d ≤ c)
    (h : decision a b (x - sign b * c)) :
    decision a b (x - sign b * d) := by
  rcases lt_or_eq_of_le hdc with hlt | heq
  · left
    rcases h with h | ⟨h, _⟩ <;> cases b <;> simp_all [sign] <;> linarith
  · simpa only [heq] using h

theorem CoreAdmissible.mono {y : CoarseData V n} {q : Tilt n} {T U φ ψ p : ℝ}
    (h : CoreAdmissible y q T φ p) (hT : 0 < T) (hTU : T ≤ U)
    (hψφ : ψ ≤ φ) (hp : 0 ≤ p) : CoreAdmissible y q U ψ p := by
  have hi : U⁻¹ ≤ T⁻¹ := inv_anti₀ hT hTU
  have he : 0 ≤ edgeScale (Fintype.card V) p := by unfold edgeScale; positivity
  refine ⟨h.regularity, ?_, ?_, ?_, h.positive, ?_, ?_,
    fun s => hψφ.trans (h.conditioning s), h.solves⟩
  · intro s
    exact (mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg _)).trans (h.sizes s)
  · intro r
    exact (h.imbalances r).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hTU (Nat.cast_nonneg _)) (Real.sqrt_nonneg _))
  · intro s t
    exact (h.edge_scale s t).trans (mul_le_mul_of_nonneg_right hTU he)
  · intro s r
    exact decision_margin_mono _ _ (mul_le_mul_of_nonneg_right hi he) (h.separation s r)
  · intro s t
    exact (h.tilt s t).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hTU hp) (Real.sqrt_nonneg _))

theorem decision_of_strict_margin (a b : Bool) {x c : ℝ}
    (h : c < sign b * x) : decision a b (x - sign b * c) := by
  left
  cases b <;> simp_all [sign]
  linarith

theorem Admissible.mono {y : CoarseData V n} {q : Tilt n} {T U φ ψ p : ℝ}
    (h : Admissible y q T φ p) (hT : 0 < T) (hTU : T ≤ U)
    (hψφ : ψ ≤ φ) (hp : 0 ≤ p) : Admissible y q U ψ p := by
  have hi : U⁻¹ ≤ T⁻¹ := inv_anti₀ hT hTU
  have he : 0 ≤ edgeScale (Fintype.card V) p := by unfold edgeScale; positivity
  refine ⟨h.regularity, ?_, ?_, ?_, h.positive, ?_, ?_,
    fun s => hψφ.trans (h.conditioning s), h.solves, ?_⟩
  · intro s
    exact (mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg _)).trans (h.sizes s)
  · intro r
    exact (h.imbalances r).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hTU (Nat.cast_nonneg _)) (Real.sqrt_nonneg _))
  · intro s t
    exact (h.edge_scale s t).trans (mul_le_mul_of_nonneg_right hTU he)
  · intro s r
    exact decision_margin_mono _ _ (mul_le_mul_of_nonneg_right hi he) (h.separation s r)
  · intro s t
    exact (h.tilt s t).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hTU hp) (Real.sqrt_nonneg _))
  · intro s b
    exact ⟨hψφ.trans (h.split s b).1, (h.split s b).2.trans (by linarith)⟩

end MajorityDynamics.Local
