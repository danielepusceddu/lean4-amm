import «Tokens»
import «AMMSet»
import «State»
open BigOperators

/- It's important to use 'rev' here because
   mathlib theorems use the form:
   ∑ x in s, f x
   So using (as a) t would be bad as a wouldn't be the last parameter.
-/
def AccountSet.supply (as: AccountSet) (t: Token): NNReal :=
  ∑ a in as.support, as.rev t a

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