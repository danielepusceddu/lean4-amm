import AMMLib.State.Tokens
import AMMLib.State.AMMs
import AMMLib.State.AMMsNN
import AMMLib.State.State
import AMMLib.State.Supply
import AMMLib.State.Networth
import AMMLib.Transaction.Swap.Rate

structure Swap
  (sx: SX) (s: Γ) (a: A) (t0 t1: T) (v0: ℝ>0)
  where
  enough: v0 ≤ s.atoms.get a t0
  exi: s.amms.init t0 t1
  nodrain: v0*(sx v0 (s.amms.r0 t0 t1 exi) (s.amms.r1 t0 t1 exi))
           < (s.amms.r1 t0 t1 exi)

theorem Swap.singleton
  (sw0: Swap sx s a t0 t1 x)
  (sw1: Swap sx s a t0 t1 x):
  sw0 = sw1 := by
    cases sw0
    cases sw1
    rfl

def Swap.rate (sw: Swap sx s a t0 t1 v0): ℝ>0
  := sx v0 (s.amms.r0 t0 t1 sw.exi) (s.amms.r1 t0 t1 sw.exi)

def Swap.y (sw: Swap sx s a t0 t1 v0): ℝ>0
  := v0*sw.rate

theorem Swap.y_eq (s: Swap sx s a t0 t1 x):
  s.y = x*s.rate := by rfl

theorem Swap.y_lt_r1 (sw: Swap sx s a t0 t1 v0):
  sw.y < s.amms.r1 t0 t1 sw.exi := by exact sw.nodrain

theorem Swap.y_lt_r1₀ (sw: Swap sx s a t0 t1 v0):
  sw.y < s.amms.r1₀ t0 t1 := by
    rw [← AMMs.r1_toNNReal _ _ _ sw.exi]
    exact sw.nodrain

noncomputable def Swap.apply (sw: Swap sx s a t0 t1 v0): Γ :=
  ⟨
    (s.atoms.sub a t0 v0 sw.enough).add a t1 sw.y,
    s.mints,
    (s.amms.sub_r1 t0 t1 sw.exi sw.y sw.nodrain).add_r0 t0 t1 (by simp[sw.exi]) v0
  ⟩

def Swap.is_solution (sw: Swap sx s a t0 t1 x₀) (o: O): Prop :=
  ∀ (x: ℝ>0) (sw2: Swap sx s a t0 t1 x),
  x ≠ x₀ → (s.mints.get a).get t0 t1 = 0 → a.gain o s sw2.apply <  a.gain o s sw.apply

@[simp] theorem Swap.atoms (sw: Swap sx s a t0 t1 v0):
  sw.apply.atoms = (s.atoms.sub a t0 v0 sw.enough).add a t1 sw.y :=
  by simp [apply]

@[simp] theorem Swap.mints (sw: Swap sx s a t0 t1 v0):
  sw.apply.mints = s.mints :=
  by simp [apply]

@[simp] theorem Swap.amms (sw: Swap sx s a t0 t1 v0):
  sw.apply.amms = (s.amms.sub_r1 t0 t1 sw.exi sw.y sw.nodrain).add_r0 t0 t1 (by simp[sw.exi]) v0 :=
  by simp [apply]

/- These simp theorems are useful because Swap.atoms
   has more than one operation, so the simplifier needs sw.exi.dif -/
@[simp] theorem Swap.b0_self
  (sw: Swap sx s a t0 t1 v0):
  (sw.apply).atoms.get a t0 = s.atoms.get a t0 - v0 := by
  simp [sw.exi.dif]

@[simp] theorem Swap.b1_self
  (sw: Swap sx s a t0 t1 v0):
  (sw.apply).atoms.get a t1 = s.atoms.get a t1 + sw.y := by
  unfold apply
  simp [sw.exi.dif]

@[simp] theorem Swap.drain_atoms
  (sw: Swap sx s a t0 t1 v0) (a': A):
  ((sw.apply.atoms.get a').drain t0).drain t1 = ((s.atoms.get a').drain t0).drain t1 := by
  unfold apply;
  rcases Decidable.em (a=a') with eq|neq
  . rw [W₀.drain_comm];
    simp only [eq, S₀.get_add_self, S₀.get_sub_self, W₀.drain_add_self, ne_eq]
    rw [W₀.drain_comm]
    simp
  . simp [neq]

@[simp] theorem Swap.mintsupply
  (sw: Swap sx s a t0 t1 v0)
  (t0' t1': T):
  sw.apply.mintsupply t0' t1' = s.mintsupply t0' t1' := by
  simp [Swap.apply, Γ.mintsupply]
