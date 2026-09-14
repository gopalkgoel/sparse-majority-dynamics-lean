import MajorityDynamics.GraphProcess.FineState.Reconstruction

/-! Prefix projection is a deterministic function of the present fine state. -/
noncomputable section
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.FineState
open Universal History
variable {V : Type*} [Fintype V] {l m n : ℕ}

def historyPrefix (hmn : m ≤ n) (s : Universal.History (n + 1)) : Universal.History (m + 1) :=
  (bits (m + 1)).symm (fun r => bits (n + 1) s (Fin.castLE (Nat.succ_le_succ hmn) r))

@[simp] theorem bits_prefix (hmn : m ≤ n) (s : Universal.History (n + 1))
    (r : Fin (m + 1)) : bits (m + 1) (historyPrefix hmn s) r =
      bits (n + 1) s (Fin.castLE (Nat.succ_le_succ hmn) r) := by simp [historyPrefix]

@[simp] theorem prefix_refl (s : Universal.History (n + 1)) : historyPrefix (le_refl n) s = s := by
  apply (bits (n + 1)).injective
  funext r
  simp

theorem prefix_trans (hlm : l ≤ m) (hmn : m ≤ n) (s : Universal.History (n + 1)) :
    historyPrefix hlm (historyPrefix hmn s) = historyPrefix (hlm.trans hmn) s := by
  apply (bits (l + 1)).injective
  funext r
  simp

@[simp] theorem prefix_actualHistory (hmn : m ≤ n) (G : SimpleGraph V) (c : V → Bool) :
    historyPrefix hmn ∘ actualHistory G c (n + 1) = actualHistory G c (m + 1) := by
  funext v
  apply (bits (m + 1)).injective
  funext r
  simp only [Function.comp_apply, bits_prefix, bits_actualHistory, Fin.val_castLE]

def projectedDegrees (hmn : m ≤ n) (σ : State V n) : V → Universal.History (m + 1) → ℤ :=
  fun v u => ∑ t ∈ block (historyPrefix hmn) u, σ.deg v t

theorem projectedDegrees_realizer (hmn : m ≤ n) (σ : State V n) (G : SimpleGraph V)
    (hG : degreeArray σ.part G = σ.deg) :
    degreeArray (historyPrefix hmn ∘ σ.part) G = projectedDegrees hmn σ := by
  funext v u
  rw [degreeArray_coarsen, hG]
  rfl

def project (hmn : m ≤ n) (σ : State V n) : State V m where
  part := historyPrefix hmn ∘ σ.part
  deg := projectedDegrees hmn σ
  realizable := by
    obtain ⟨G, hG⟩ := σ.realizable
    exact ⟨G, projectedDegrees_realizer hmn σ G hG⟩
  history := by
    obtain ⟨G, c, rfl⟩ := attained σ
    have hd := projectedDegrees_realizer hmn (actualState G c n) G rfl
    rw [actualState_part, prefix_actualHistory] at hd ⊢
    rw [← hd]
    exact actualRow_historyEvent G c m

@[simp] theorem project_part (hmn : m ≤ n) (σ : State V n) :
    (project hmn σ).part = historyPrefix hmn ∘ σ.part := rfl

@[simp] theorem project_deg (hmn : m ≤ n) (σ : State V n) (v : V)
    (u : Universal.History (m + 1)) :
    (project hmn σ).deg v u = ∑ t ∈ block (historyPrefix hmn) u, σ.deg v t := rfl

@[simp] theorem project_actualState (hmn : m ≤ n) (G : SimpleGraph V) (c : V → Bool) :
    project hmn (actualState G c n) = actualState G c m := by
  apply State.ext
  · exact prefix_actualHistory hmn G c
  · change projectedDegrees hmn (actualState G c n) = degreeArray (actualHistory G c (m + 1)) G
    have hd := projectedDegrees_realizer hmn (actualState G c n) G rfl
    simpa only [actualState_part, prefix_actualHistory] using hd.symm

@[simp] theorem project_refl (σ : State V n) : project (le_refl n) σ = σ := by
  obtain ⟨G, c, rfl⟩ := attained σ
  exact project_actualState _ G c

theorem project_trans (hlm : l ≤ m) (hmn : m ≤ n) (σ : State V n) :
    project hlm (project hmn σ) = project (hlm.trans hmn) σ := by
  obtain ⟨G, c, rfl⟩ := attained σ
  simp only [project_actualState]

end MajorityDynamics.GraphProcess.FineState
