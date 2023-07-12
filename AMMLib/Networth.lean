import AMMLib.Wallets.MintedWall
import AMMLib.Wallets.AtomicWall
import AMMLib.State

/-
mintsupply that returns PReal:
Finsupp.add_sum_erase

in a reachable state
if s.amms.init t0 t1, then there must exist an A in s.mints such that s.mints t0 t1 ≠ 0
choose that, destruct the supply and we'll get: 
s.mints t0 t1 + ((s.mints.drain a t0 t1).supply t0 t1)
which must be positive

this will turn Γ.T₁Price into a PReal
however, W₀.worth and W₁.worth will remain NNReals 
so is it worth it?
-/

noncomputable def Γ.T₁Price
(s: Γ) (o: T → PReal)
(t0 t1: T): NNReal :=
  if h:s.amms.init t0 t1 then 
  ((s.amms.r0 t0 t1 h)*(o t0) + (s.amms.r1 t0 t1 h)*(o t1)) / (s.mints.supply t0 t1)
  else 0

theorem Γ.T₁Price_reorder (s: Γ) (o: T → PReal) (t1 t0: T):
  s.T₁Price o t1 t0 = s.T₁Price o t0 t1 := by
  unfold Γ.T₁Price
  rcases Decidable.em (s.amms.init t0 t1) with init|uninit
  . simp only [init, init.swap, dite_true]
    rw [Sₐ.r0_reorder _ t1 t0, Sₐ.r1_reorder _ t1 t0, 
        add_comm, S₁.supply_reorder]
  . have b := (Sₐ.init_swap_iff s.amms t0 t1).not
    simp [uninit, b.mp uninit]

noncomputable def Γ.networth
(s: Γ) (a: A) (o: T → PReal): NNReal
:=
(W₀.worth (s.atoms.get a) o)
+
(W₁.worth (s.mints.get a) (s.T₁Price o))

noncomputable def A.gain
(a: A) (o: T → PReal) (s s': Γ)
: ℝ
:= ((s'.networth a o): ℝ) - ((s.networth a o): ℝ)
