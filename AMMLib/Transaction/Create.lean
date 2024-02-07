import AMMLib.State.AMMs
import AMMLib.State.State
import AMMLib.State.Supply

structure Create (s: Γ) (t0 t1: T) (a: A) (v0 v1: ℝ>0) where
  -- Tokens must be different to form a valid minted token
  hdif: t0 ≠ t1

  -- AMM does not exist in s
  hnin: ¬s.amms.init t0 t1

  -- User has enough balance of t0 and t1
  hen0: v0 ≤ s.atoms.get a t0
  hen1: v1 ≤ s.atoms.get a t1

noncomputable def Create.apply
{s: Γ} (v: Create s t0 t1 a v0 v1): Γ :=
  ⟨
  -- Subtract v0:t0 and v1:t1 from a's atomic wallet
  (s.atoms.sub a t0 v0 v.hen0
  ).sub a t1 v1 (by simp[v.hen1, v.hdif]),

  -- Add v0:{t0,t1} t0 a's minted wallet
  s.mints.add a t0 t1 v.hdif v0,

  -- Initialize an AMM {v0:t0, v1:t1}
  s.amms.initialize v.hdif v0 v1
  ⟩

@[simp] theorem Create.supply_minted_diff'
{s: Γ} (v: Create s t0 t1 a r0 r1)
(t0' t1': T) (hdifp: diffmint t0 t1 t0' t1'):
v.apply.mints.supply t0' t1' = s.mints.supply t0' t1' := by
  simp [apply, Γ.mintsupply, hdifp]

@[simp] theorem Create.supply_minted_diff
{s: Γ} (v: Create s t0 t1 a r0 r1)
(t0' t1': T) (hdifp: diffmint t0 t1 t0' t1'):
v.apply.mintsupply t0' t1' = s.mintsupply t0' t1' := by
  simp [apply, Γ.mintsupply, hdifp]

@[simp] theorem Create.init_same (v: Create s t0 t1 a r0 r1) (t0' t1': T) (same: samemint t0 t1 t0' t1'): v.apply.amms.init t0' t1' := by
  rcases same with ⟨a,b⟩|⟨a,b⟩
  . simp [← a, ← b, apply]
  . apply AMMs.init.swap
    simp [← a, ← b, apply]

@[simp] theorem Create.init_diff_iff
  {s: Γ} (v: Create s t0 t1 a r0 r1) (t0' t1': T) (hdifp: diffmint t0 t1 t0' t1'):
  v.apply.amms.init t0' t1' ↔ s.amms.init t0' t1'
  :=
  by simp [apply, hdifp]
