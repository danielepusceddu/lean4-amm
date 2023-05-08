import «Tokens»
import «AMMSet»
import «State»
open BigOperators

def AccountSet.supply (as: AccountSet) (t: Token): NNReal :=
  ∑ a in as.support, (as a) t

noncomputable def AMMSet.supply (amms: AMMSet) (t: AtomicTok): NNReal :=
  amms.map.sum (λ amm => 
    if h:t ∈ amm.f.supp
    then amm.r0 ⟨t, h⟩
    else 0)

noncomputable def State.supply (s: State) (t: Token): NNReal
  := match t with
  | Token.Atomic t' => (s.accs.supply t) + (s.amms.supply t')
  | Token.Minted _ => s.accs.supply t