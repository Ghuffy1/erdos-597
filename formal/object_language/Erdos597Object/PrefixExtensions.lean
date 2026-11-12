import Erdos597Object.SystemGluing
import Mathlib.Order.Hom.WithTopBot

set_option backward.isDefEq.respectTransparency false

/-! Successor and limit extensions of compatible closed prefixes. -/

namespace Erdos597Object.PrefixExtensions

open Set Order Cardinal
open scoped Cardinal
open IterationSystems SystemRestrictions SystemGluing

variable {J : Type} [LinearOrder J]

theorem map_heq_of_indices {I : Type} [Preorder I] (S : System I)
    {a b c d : I} (ha : a = c) (hb : b = d) (hab : a ≤ b) (hcd : c ≤ d) :
    HEq (S.map a b hab) (S.map c d hcd) := by
  cases ha
  cases hb
  rfl

theorem prefixIso_symm_of_lt (j : J) (a : Iic j) (h : a.val < j) :
    (SystemReindexing.prefixIso j).symm a = (⟨a.val, h⟩ : Iio j) := by
  change SystemReindexing.lowerPoint j a = _
  simp only [SystemReindexing.lowerPoint, dif_pos h]

theorem closePrefix_restrict [WellFoundedLT J] {i j : J} (hij : i < j)
    (hj : IsSuccLimit j) (S : System (Iio j))
    (hS : ExtensionContinuity.Continuous S.map)
    (hcard : #(Iio j) ≤ IterationCardinals.iterationSize) :
    restrict (S.closePrefix j hj hS hcard) hij.le =
      S.reindex (fun a : Iic i => (⟨a.val, a.property.trans_lt hij⟩ : Iio j))
        (fun _ _ h => h) := by
  letI : Nonempty (Iio j) := hj.nonempty_Iio.to_subtype
  apply System.ext
  · funext a
    change (S.limit hS hcard).obj ((SystemReindexing.prefixIso j).symm
      ⟨a.val, a.property.trans hij.le⟩) = S.obj _
    rw [prefixIso_symm_of_lt j _ (a.property.trans_lt hij)]
    rfl
  · intro a b hab
    change HEq ((S.limit hS hcard).map
      ((SystemReindexing.prefixIso j).symm ⟨a.val, a.property.trans hij.le⟩)
      ((SystemReindexing.prefixIso j).symm ⟨b.val, b.property.trans hij.le⟩) _)
      (S.map _ _ _)
    exact map_heq_of_indices (S.limit hS hcard)
      (prefixIso_symm_of_lt j _ (a.property.trans_lt hij))
      (prefixIso_symm_of_lt j _ (b.property.trans_lt hij))
      ((SystemReindexing.prefixIso j).symm.monotone hab) (WithTop.coe_le_coe.mpr hab)

section Successor

variable [SuccOrder J] [NoMaxOrder J]

def successorOpenIso (i : J) : Iic i ≃o Iio (succ i) where
  toFun a := ⟨a.val, lt_succ_of_le a.property⟩
  invFun a := ⟨a.val, le_of_lt_succ a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

def successorIso (i : J) : WithTop (Iic i) ≃o Iic (succ i) :=
  (successorOpenIso i).withTopCongr.trans (SystemReindexing.prefixIso (succ i))

theorem successorIso_coe (i : J) (a : Iic i) :
    successorIso i a = ⟨a.val, a.property.trans (le_succ i)⟩ := rfl

theorem successorIso_symm_coe (i : J) (a : Iic i) :
    (successorIso i).symm ⟨a.val, a.property.trans (le_succ i)⟩ = (a : WithTop (Iic i)) := by
  have h := congrArg (successorIso i).symm (successorIso_coe i a)
  simpa only [OrderIso.symm_apply_apply] using h.symm

noncomputable def successorPrefix {L : Type} (i : J) (S : Prefix i)
    (Q : BooleanIteration.BooleanPoset (S.system.obj ⟨i, le_rfl⟩) L)
    (hccc : MartinTransport.CountableChainCondition (BooleanIteration.Condition Q))
    (hL : #L ≤ ℵ₁) (hcover : (⨆ a, Q.member a) = ⊤) : Prefix (succ i) where
  system := (S.system.successor ⟨i, le_rfl⟩ (fun a => a.property) Q hccc hL hcover).reindex
    (successorIso i).symm (successorIso i).symm.monotone
  continuous := SystemReindexing.pullback_continuous _ _
    (S.system.successor_continuous ⟨i, le_rfl⟩ (fun a => a.property) Q hccc hL hcover
      S.continuous)

theorem successorPrefix_restrict {L : Type} (i : J) (S : Prefix i)
    (Q : BooleanIteration.BooleanPoset (S.system.obj ⟨i, le_rfl⟩) L)
    (hccc : MartinTransport.CountableChainCondition (BooleanIteration.Condition Q))
    (hL : #L ≤ ℵ₁) (hcover : (⨆ a, Q.member a) = ⊤) :
    (successorPrefix i S Q hccc hL hcover).restrict (le_succ i) = S := by
  apply Prefix.ext
  apply System.ext
  · funext a
    change (S.system.successor ⟨i, le_rfl⟩ (fun a => a.property) Q hccc hL hcover).obj
      ((successorIso i).symm ⟨a.val, a.property.trans (le_succ i)⟩) = S.system.obj a
    rw [successorIso_symm_coe]
    rfl
  · intro a b hab
    change HEq ((S.system.successor ⟨i, le_rfl⟩ (fun a => a.property) Q hccc hL hcover).map
      ((successorIso i).symm ⟨a.val, a.property.trans (le_succ i)⟩)
      ((successorIso i).symm ⟨b.val, b.property.trans (le_succ i)⟩) _) (S.system.map a b hab)
    exact map_heq_of_indices
      (S.system.successor ⟨i, le_rfl⟩ (fun a => a.property) Q hccc hL hcover)
      (successorIso_symm_coe i a) (successorIso_symm_coe i b)
      ((successorIso i).symm.monotone hab) (WithTop.coe_le_coe.mpr hab)

end Successor

section Limit

variable [WellFoundedLT J]

noncomputable def limitPrefix (j : J) (hj : IsSuccLimit j)
    (S : ∀ i : Iio j, Prefix i.val)
    (hS : ∀ (i k : Iio j) (hik : i ≤ k), (S k).restrict hik = S i)
    (hcard : #(Iio j) ≤ IterationCardinals.iterationSize) : Prefix j := by
  let systems : ∀ i : Iio j, System (Iic i.val) := fun i => (S i).system
  have hsystems : ∀ (i k : Iio j) (hik : i ≤ k), restrict (systems k) hik = systems i :=
    fun i k hik => congrArg Prefix.system (hS i k hik)
  let old := glue systems hsystems
  have hold : ExtensionContinuity.Continuous old.map :=
    glue_continuous systems hsystems (isLowerSet_Iio j) (fun i => (S i).continuous)
  exact ⟨old.closePrefix j hj hold hcard, old.closePrefix_continuous j hj hold hcard⟩

theorem limitPrefix_restrict (j : J) (hj : IsSuccLimit j)
    (S : ∀ i : Iio j, Prefix i.val)
    (hS : ∀ (i k : Iio j) (hik : i ≤ k), (S k).restrict hik = S i)
    (hcard : #(Iio j) ≤ IterationCardinals.iterationSize) (i : Iio j) :
    (limitPrefix j hj S hS hcard).restrict i.property.le = S i := by
  apply Prefix.ext
  unfold limitPrefix
  dsimp only [Prefix.restrict]
  rw [closePrefix_restrict i.property hj]
  exact glue_restrict (fun i => (S i).system)
    (fun i k hik => congrArg Prefix.system (hS i k hik)) (isLowerSet_Iio j) i

end Limit

end Erdos597Object.PrefixExtensions
