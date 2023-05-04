import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Algebra.BigOperators.Basic
import «Helpers»
import «PReal»
import «Tokens»
import «AMMSet»
open Token
open BigOperators

abbrev State        := AccountSet × AMMSet
def State.accounts (s: State) := s.fst
abbrev State.amms     (s: State) := s.snd
def State.amm (s: State) (amm: MintedTok) := (s.snd).map.f amm

def SwapRate := PReal → PReal → PReal → PReal
noncomputable def constprod: SwapRate := λ x r0 r1 => r1 / (r0 + x)

def swap_amount (sx: SwapRate) (x r0 r1: PReal)
  := x*(sx x r0 r1)

noncomputable def swap0
  (sx: SwapRate) (a: Account) 
  (v0: PReal) (t0 t1: AtomicTok) (s: State)
  (_: v0.1 ≤ (s.accounts a) t0) /- UNUSED MINIMUM BALANCE PRECONDITION -/
  (exi: s.amms.map' t0 t1 ≠ none)
  (nodrain: swap_amount sx v0 (get_r0 exi) (get_r1 exi) < get_r1 exi)
  : State :=
  have ht   := map'_not_none_imp_diff s.amms t0 t1 exi
  have ht0  := amm_of_pair_imp_t0_belongs' exi
  have ht1  := amm_of_pair_imp_t1_belongs' exi
  let amm  := get_amm exi
  let r0   := get_r0 exi
  let r1   := get_r1 exi
  let swam := swap_amount sx v0 r0 r1
  let w    := s.accounts a
  let w'   := w.update (Atomic t0) ((w (Atomic t0)) - v0.toNNReal)
  let w''  := w'.update (Atomic t1) ((w' (Atomic t1)) + swam)
  let amm' := amm.sub t1 swam ht1 nodrain
  let amm'':= amm'.add t0 v0 (AMM.sub.still_belongs ht1 nodrain t0 ht0)

  (s.accounts.update a w'',
   s.amms.update ⟨⟦(t0,t1)⟧,ht⟩ amm'' (by
   have hamm'': amm'' = amm'.add t0 v0 (AMM.sub.still_belongs ht1 nodrain t0 ht0) := by simp
   rw [hamm'']
   rw [← @AMM.add.t0_same amm' t0 v0 (AMM.sub.still_belongs ht1 nodrain t0 ht0)]
   rw [← @AMM.add.t1_same amm' t0 v0 (AMM.sub.still_belongs ht1 nodrain t0 ht0)]
   have hamm': amm' = amm.sub t1 swam ht1 nodrain := by simp
   rw [hamm']
   rw [← @AMM.sub.t0_same amm t1 swam ht1 nodrain]
   rw [← @AMM.sub.t1_same amm t1 swam ht1 nodrain]
   have hamm: amm = get_amm exi := by simp
   rw [hamm]; clear hamm hamm' hamm'';
   exact get_amm_lemma exi
  ))

noncomputable def supply (s: State) (t: Token): NNReal :=
  match t with
  | Atomic t' => 
    ∑ a in s.accounts.support, (s.accounts a) t +
    s.amms.map.sum (λ amm => if h:t'=amm.t0 ∨ t'=amm.t1
                           then ((amm.r t' h): NNReal)
                           else 0)
  | Minted _ => 
    ∑ a in s.accounts.support, (s.accounts a) t
