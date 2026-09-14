import MajorityDynamics.GraphProcess.DayOne.Algebra

noncomputable section
namespace MajorityDynamics.GraphProcess.DayOne
open Universal Idealized Idealized.LinearResponse Idealized.PerturbedTilt
open Idealized.PerturbedEvolution

variable {V : Type*} [Fintype V]

theorem faithful_of_initial_errors {N : ℕ} {p : Binomial.Probability} {T τ δ : ℝ}
    {a : Process.Data} (ha : a.state 0 = Process.initialState N p)
    (hN : 1 ≤ N) (hT : 1 ≤ T) (hτ0 : 0 ≤ τ) (hτT : τ ≤ T)
    (y : Local.CoarseData V 0) (hreg : y.reg = true)
    (hszN : ∀ s, y.sizes s ≤ N)
    (hs : ∀ s, |(y.sizes s : ℝ)-((N/2 : ℕ) : ℝ)-τ*Real.sqrt N*ε 0 s| ≤ 2)
    (he : ∀ s t, |y.realEdges s t-(p : ℝ)*(y.sizes s : ℝ)*
      ((y.sizes t : ℝ)-(if s=t then 1 else 0))| ≤
      2*(N : ℝ)*Real.sqrt (p : ℝ)*Real.log N)
    (hsabs : 2 ≤ Real.sqrt N*(N : ℝ)^(-δ))
    (heabs : 2*(N : ℝ)*Real.sqrt (p : ℝ)*Real.log N +
      (20*(T+1)^2)*(N : ℝ)*(p : ℝ) ≤
      betaScale N p 0*(N : ℝ)^(-δ)*(N : ℝ)^2*(p : ℝ)) :
    Faithful N p 1 δ τ a y := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have ha0 : (0 : ℝ) ≤ (N/2 : ℕ) := Nat.cast_nonneg _
  have haN : ((N/2 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N 2
  have hodd : |(N : ℝ)-2*((N/2 : ℕ) : ℝ)| ≤ 1 := by
    have hmod := Nat.mod_lt N (by omega : 0 < 2)
    have hid := Nat.mod_add_div N 2
    have hlo : (2 : ℝ)*(N/2 : ℕ) ≤ N := by exact_mod_cast (show 2*(N/2) ≤ N by omega)
    have hhi : (N : ℝ) ≤ 2*(N/2 : ℕ)+1 := by exact_mod_cast (show N ≤ 2*(N/2)+1 by omega)
    rw [abs_of_nonneg (by linarith)]
    linarith
  have heps : ∀ s : Universal.History 1, |ε 0 s| = 1 := by
    intro s
    rw [ε_zero]
    cases last s <;> norm_num [sign]
  refine ⟨hreg, ?_, ?_⟩
  · intro s
    simpa only [ha,Process.initialState,sizeScale,pow_zero,mul_one,one_mul,
      Local.CoarseData.integerSizes, Int.cast_natCast]
      using (hs s).trans hsabs
  · intro s t
    have hcenter := centering_error hn (Real.one_le_sqrt.mpr hn) (Real.sq_sqrt hn0)
      ha0 haN hodd hτ0 hτT hT (heps s) (heps t)
      (show (0 : ℝ) ≤ (if s=t then 1 else 0) by split_ifs <;> norm_num)
      (show (if s=t then (1:ℝ) else 0) ≤ 1 by split_ifs <;> norm_num)
      (Nat.cast_nonneg (y.sizes s))
      (show (y.sizes s : ℝ) ≤ N by exact_mod_cast hszN s) (hs s) (hs t)
    have hcenterp := mul_le_mul_of_nonneg_left hcenter p.property.1.le
    have htriangle := abs_sub_le (y.realEdges s t)
      ((p : ℝ)*(y.sizes s : ℝ)*((y.sizes t : ℝ)-(if s=t then 1 else 0)))
      ((p : ℝ)*((N/2 : ℕ) : ℝ)*(((N/2 : ℕ) : ℝ)-(if s=t then 1 else 0))*
        (1+τ/Real.sqrt N*(2*ε 0 s+2*ε 0 t)))
    have hsecond : |(p : ℝ)*(y.sizes s : ℝ)*((y.sizes t : ℝ)-(if s=t then 1 else 0))-
      (p : ℝ)*((N/2 : ℕ) : ℝ)*(((N/2 : ℕ) : ℝ)-(if s=t then 1 else 0))*
        (1+τ/Real.sqrt N*(2*ε 0 s+2*ε 0 t))| ≤ (20*(T+1)^2)*(N : ℝ)*(p : ℝ) := by
      calc
        _ = |(p : ℝ)*((y.sizes s : ℝ)*((y.sizes t : ℝ)-(if s=t then 1 else 0))-
          ((N/2 : ℕ) : ℝ)*(((N/2 : ℕ) : ℝ)-(if s=t then 1 else 0))*
          (1+τ/Real.sqrt N*(2*ε 0 s+2*ε 0 t)))| := by congr 1; ring
        _ = (p : ℝ)*|(y.sizes s : ℝ)*((y.sizes t : ℝ)-(if s=t then 1 else 0))-
          ((N/2 : ℕ) : ℝ)*(((N/2 : ℕ) : ℝ)-(if s=t then 1 else 0))*
          (1+τ/Real.sqrt N*(2*ε 0 s+2*ε 0 t))| := by
            rw [abs_mul, abs_of_pos p.property.1]
        _ ≤ _ := by nlinarith [hcenterp]
    have hh := (htriangle.trans (add_le_add (he s t) hsecond)).trans heabs
    change |y.realEdges s t - (a.state 0).edges s t *
      (1+τ*betaScale N p 0*(ε 0 s/ν 0 s+ε 0 t/ν 0 t))| ≤ _
    simp only [ha,Process.initialState,betaScale,pow_zero,one_mul,ν_zero] at hh ⊢
    convert hh using 1
    congr 1
    ring

end MajorityDynamics.GraphProcess.DayOne
