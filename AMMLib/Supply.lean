import AMMLib.Tokens
import AMMLib.AMMSet
import AMMLib.State
import AMMLib.Finsupp2
open BigOperators

def pick2 {α β: Type} (_: α) (x: β) := x

theorem pick2_zero {α β: Type} [Zero β]
: ∀ (a: α), pick2 a (0: β) = (0: β) := by simp [pick2]

theorem pick2_add {α β: Type} [AddZeroClass β]
: ∀ (a: α) (b1 b2: β),
pick2 a (b1+b2) = (pick2 a b1) + (pick2 a b2) := by simp [pick2]

noncomputable def AtomicWalls.supply 
(ws: AtomicWalls) (t: AtomicTok)
: NNReal :=
  (ws.curried_swap t).sum pick2

noncomputable def MintedWalls.supply 
(ws: MintedWalls) (t: MintedTok)
: NNReal :=
  (ws.curried_swap t).sum pick2

@[simp] lemma MintedWalls.supply_up_diff 
(as: MintedWalls) (t: MintedTok) (a: Account) (t': MintedTok) 
(v: NNReal) (hdif: t ≠ t'):
  supply (as.up a t' v) t = as.supply t := by 
  unfold supply
  rw [Finsupp.up_swap as a t' v]
  rw [Finsupp.up_diff _ _ _ _ _ hdif]

noncomputable def AMMSet.supply (amms: AMMSet) (t: AtomicTok): NNReal := (amms.f t).sum λ _ x => x.fst

noncomputable def State.atomsupply 
(s: State) (t: AtomicTok): NNReal :=
  (s.atoms.supply t) + (s.amms.supply t)

noncomputable def State.mintsupply
(s: State) (t: MintedTok): NNReal :=
  s.mints.supply t

@[simp] theorem AtomicWalls.supply_addb_same 
(as: AtomicWalls) (t: AtomicTok) (a: Account) (x: NNReal)
: (as.addb a t x).supply t = x + (as.supply t) := by

  simp [supply, addb, Finsupp.up_swap]
  simp [Finsupp.up_eq]
  rw [Finsupp.update_eq_single_add_erase]

  rw [@Finsupp.sum_add_index' _ _ _ _ _ _ _ pick2 pick2_zero pick2_add]
  rw [Finsupp.sum_single_index (pick2_zero a)]
  rw [pick2_add]
  rw [add_comm (pick2 a (as a t))]
  rw [add_assoc]
  rw [← Finsupp.curried_swap_def as]
  rw [Finsupp.add_sum_erase']
  . simp [pick2]
  . exact pick2_zero

@[simp] theorem MintedWalls.supply_addb_same 
(as: MintedWalls) (t: MintedTok) (a: Account) (x: NNReal)
: (as.addb a t x).supply t = x + (as.supply t) := by

  simp [supply, addb, Finsupp.up_swap]
  simp [Finsupp.up_eq]
  rw [Finsupp.update_eq_single_add_erase]

  rw [@Finsupp.sum_add_index' _ _ _ _ _ _ _ pick2 pick2_zero pick2_add]
  rw [Finsupp.sum_single_index (pick2_zero a)]
  rw [pick2_add]
  rw [add_comm (pick2 a (as a t))]
  rw [add_assoc]
  rw [← Finsupp.curried_swap_def as]
  rw [Finsupp.add_sum_erase']
  . simp [pick2]
  . exact pick2_zero
