import Mathlib.Data.Nat.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import «PReal»
open BigOperators

abbrev Account := ℕ
abbrev AtomicTok := ℕ

structure MintedTok where
  upair: Sym2 AtomicTok
  hdiff: ¬Sym2.IsDiag upair

instance: DecidableEq MintedTok :=
  fun x y => 
  by rcases x with ⟨p1,h1⟩
     rcases y with ⟨p2,h2⟩
     simp
     infer_instance

inductive Token where
  | Atomic: AtomicTok → Token
  | Minted: MintedTok → Token
open Token

instance : Coe AtomicTok Token where
  coe := Atomic
instance : Coe MintedTok Token where
  coe := Minted

abbrev Wallet       := Token →₀ NNReal
abbrev AccountSet   := Account →₀ Wallet
abbrev PriceOracle  := Token → PReal 

def netWorth (o: PriceOracle) (a: Wallet): NNReal :=
  ∑ t in a.support, (a t) * (o t)