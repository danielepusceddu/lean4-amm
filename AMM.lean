import «Helpers»
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
open BigOperators

abbrev Account := ℕ
abbrev AtomicTok := ℕ

structure MintedTok where
  t0: AtomicTok
  t1: AtomicTok
  ht: t0 < t1

inductive Token where
  | Atomic: AtomicTok → Token
  | Minted: MintedTok → Token
open Token

instance : Coe AtomicTok Token where
  coe := Atomic
instance : Coe MintedTok Token where
  coe := Minted

abbrev AtomicWallet := AtomicTok →₀ NNReal
abbrev MintedWallet := MintedTok →₀ NNReal
abbrev AMMSet       := MintedTok →₀ (NNReal × NNReal) 
abbrev Wallet       := Token →₀ NNReal
abbrev AccountSet   := Account →₀ Wallet
abbrev State        := AccountSet × AMMSet
abbrev AtomOracle   := AtomicTok → NNReal -- WITHOUT ZERO!!
abbrev PriceOracle  := Token → NNReal 

def State.accounts (s: State) := s.fst
abbrev State.amms     (s: State) := s.snd
def State.amm (s: State) (amm: MintedTok) := (s.snd) amm

def netWorth (o: PriceOracle) (a: Wallet): NNReal :=
  ∑ t in a.support, (a t) * (o t)

def SwapRate := NNReal → NNReal → NNReal → NNReal
noncomputable def constprod: SwapRate := λ x r0 r1 => r1 / (r0 + x)

def swap_amount (sx: SwapRate) (x r0 r1: NNReal)
  := x*(sx x r0 r1)
def swap_amount0 (sx: SwapRate) (x r0 r1: NNReal)
  := x*(sx x r0 r1)

def validswap0 (sx: SwapRate) (a: Account) 
               (v0: NNReal)   (amm: MintedTok)
               (s: State)
     -- Can't offer 0 tokens         
  := v0 ≠ 0 
     -- Account should have the tokens offered
   ∧ v0 ≤ (s.accounts a) amm.t0
     -- Swap shouldn't drain the amm
   ∧ swap_amount sx v0 (s.amms amm).fst (s.amms amm).snd < (s.amms amm).snd

noncomputable def swap0 (sx: SwapRate) (a: Account) 
          (v0: NNReal) (amm: MintedTok) (s: State)
          (_: validswap0 sx a v0 amm s): State :=
  let r0   := (s.amms amm).fst
  let r1   := (s.amms amm).snd
  let swam := swap_amount sx v0 r0 r1
  let w   := s.accounts a
  let w'  := w.update amm.t0 ((w amm.t0) - v0)
  let w'' := w'.update amm.t1 ((w' amm.t1) + swam)

  (s.accounts.update a w'',
   s.amms.update amm (r0+v0, r1-swam))


def constrprodProof (a: Account) 
  (v0: NNReal) (amm: MintedTok) (s: State)
  (h: validswap0 constprod a v0 amm s)
  : let s' := swap0 constprod a v0 amm s h
    (s.amms amm).fst * (s.amms amm).snd
    =
    (s'.amms amm).fst * (s'.amms amm).snd := 
  
  by simp [swap0, State.amms, Finsupp.update, Function.update, swap_amount, constprod]
     unfold validswap0 swap_amount constprod at h
     rcases h with ⟨v0neq0, v0leqbalance, nodrain⟩

     -- Lift everything to a real
     rewrite [← NNReal.eq_iff]
     simp
     rewrite [NNReal.coe_sub (LT.lt.le nodrain)]

     -- Alias things to make proof states more readable
     let r0: ℝ := (s.snd amm).fst; let r1: ℝ := ↑(s.snd amm).snd
     have hr0: r0 = (s.snd amm).fst := by rfl
     have hr1: r1 = (s.snd amm).snd := by rfl
     simp [← hr0, ← hr1];

     -- Actual proof
     rewrite [div_eq_mul_inv]
     apply Eq.symm
     rewrite [← NNReal.coe_ne_zero] at v0neq0
     have hv0: 0 ≤ ↑v0 := NNReal.coe_nonneg v0
     have hneq: r0+v0 ≠ 0 := by
        apply GT.gt.ne
        have hr0': 0 ≤ r0 := NNReal.coe_nonneg (s.snd amm).fst
        apply add_pos_of_nonneg_of_pos
        . trivial
        . exact Ne.lt_of_le' v0neq0 hv0
     
     calc (r0 + v0) * (r1 - v0 * (r1*(r0 + v0)⁻¹)) 
           = 
           r0*r1 - v0*r1*((r0+v0)*(r0 + v0)⁻¹) + v0*r1 
      := by linarith
     _ =   r0*r1 - v0*r1*1 + v0*r1 
      := by rewrite [mul_inv_self_R (r0+v0)]; rfl; exact hneq
     _ =   r0*r1
      := by linarith
