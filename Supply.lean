import «Tokens»
import «AMMSet»
import «State»
import «Finsupp2»
open BigOperators

def pick2 {α β: Type} (_: α) (x: β) := x

noncomputable def AccountSet.supply (as: AccountSet) (t: Token): NNReal :=
  (as.curried_swap t).sum pick2

lemma AccountSet.supply_up_diff (as: AccountSet) (t: Token) (a: Account) (t': Token) (v: NNReal) (hdif: t ≠ t'):
  supply (as.up a t' v) t = as.supply t := by 
  unfold supply
  rw [Finsupp.up_swap as a t' v]
  rw [Finsupp.up_diff _ _ _ _ _ hdif]

noncomputable def AMMSet.supply (amms: AMMSet) (t: AtomicTok): NNReal :=
  amms.map.sum (λ amm => 
    if h:t ∈ amm.f.supp
    then amm.r0 ⟨t, h⟩
    else 0)

noncomputable def State.supply (s: State) (t: Token): NNReal
  := match t with
  | Token.Atomic t' => (s.accs.supply t) + (s.amms.supply t')
  | Token.Minted _ => s.accs.supply t

noncomputable def State.redeemrate
  (s: State) (m: MintedOf s.amms) (t: AtomicOfM m): NNReal
  := (m.amm.r0 t.ofAMM) / (s.supply m.m)