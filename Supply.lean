import «Tokens»
import «AMMSet»
import «State»
import «Finsupp2»
open BigOperators

def pick2 {α β: Type} (_: α) (x: β) := x

theorem pick2_zero {α β: Type} [Zero β]
: ∀ (a: α), pick2 a (0: β) = (0: β) := by simp [pick2]

theorem pick2_add {α β: Type} [AddZeroClass β]
: ∀ (a: α) (b1 b2: β),
pick2 a (b1+b2) = (pick2 a b1) + (pick2 a b2) := by simp [pick2]

noncomputable def AccountSet.supply (as: AccountSet) (t: Token): NNReal :=
  (as.curried_swap t).sum pick2

@[simp] lemma AccountSet.supply_up_diff (as: AccountSet) (t: Token) (a: Account) (t': Token) (v: NNReal) (hdif: t ≠ t'):
  supply (as.up a t' v) t = as.supply t := by 
  unfold supply
  rw [Finsupp.up_swap as a t' v]
  rw [Finsupp.up_diff _ _ _ _ _ hdif]

noncomputable def AMMSet.supply (amms: AMMSet) (t: AtomicTok): NNReal := (amms.f t).sum λ _ x => x.fst

noncomputable def State.supply (s: State) (t: Token): NNReal
  := match t with
  | Token.Atomic t' => (s.accs.supply t) + (s.amms.supply t')
  | Token.Minted _ => s.accs.supply t


theorem AccountSet.supply_addb_same 
(as: AccountSet) (t: Token) (a: Account) (x: NNReal)
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
