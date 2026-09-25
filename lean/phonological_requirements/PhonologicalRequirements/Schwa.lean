                        
namespace PhonologicalRequirements
namespace Schwa

def ind (b : Bool) (x : Int) : Int := if b then x else 0

def logitWord (d n wCLU wCCC wCLASH wS wDEP : Int) (cc clash : Bool) : Int :=
  ind (!cc) (d * wCLU) + ind cc (d * wCCC) + ind clash (d * wCLASH) - n * wS - d * wDEP

def logitClitic (d n wCLU wCCC wCLASH wS wMAX : Int) (cc clash : Bool) : Int :=
  ind (!cc) (n * wCLU) + ind cc (n * wCCC) + ind clash (n * wCLASH) + d * wMAX - d * wS

theorem word_effect_ccc (d n wCLU wCCC wCLASH wS wDEP : Int) (clash : Bool) :
    logitWord d n wCLU wCCC wCLASH wS wDEP true clash - logitWord d n wCLU wCCC wCLASH wS wDEP false clash
      = d * (wCCC - wCLU) := by
  cases clash <;> simp [logitWord, ind, Int.mul_sub] <;> omega

theorem clitic_effect_ccc (d n wCLU wCCC wCLASH wS wMAX : Int) (clash : Bool) :
    logitClitic d n wCLU wCCC wCLASH wS wMAX true clash - logitClitic d n wCLU wCCC wCLASH wS wMAX false clash
      = n * (wCCC - wCLU) := by
  cases clash <;> simp [logitClitic, ind, Int.mul_sub] <;> omega

theorem word_effect_clash (d n wCLU wCCC wCLASH wS wDEP : Int) (cc : Bool) :
    logitWord d n wCLU wCCC wCLASH wS wDEP cc true - logitWord d n wCLU wCCC wCLASH wS wDEP cc false
      = d * wCLASH := by
  cases cc <;> simp [logitWord, ind, Int.mul_sub] <;> omega

theorem clitic_effect_clash (d n wCLU wCCC wCLASH wS wMAX : Int) (cc : Bool) :
    logitClitic d n wCLU wCCC wCLASH wS wMAX cc true - logitClitic d n wCLU wCCC wCLASH wS wMAX cc false
      = n * wCLASH := by
  cases cc <;> simp [logitClitic, ind, Int.mul_sub] <;> omega

theorem common_ratio (d n wCLU wCCC wCLASH wS wDEP wMAX : Int) (cc clash : Bool) :
    (logitClitic d n wCLU wCCC wCLASH wS wMAX true clash - logitClitic d n wCLU wCCC wCLASH wS wMAX false clash) * d
      = (logitWord d n wCLU wCCC wCLASH wS wDEP true clash - logitWord d n wCLU wCCC wCLASH wS wDEP false clash) * n ∧
    (logitClitic d n wCLU wCCC wCLASH wS wMAX cc true - logitClitic d n wCLU wCCC wCLASH wS wMAX cc false) * d
      = (logitWord d n wCLU wCCC wCLASH wS wDEP cc true - logitWord d n wCLU wCCC wCLASH wS wDEP cc false) * n := by
  rw [clitic_effect_ccc, word_effect_ccc, clitic_effect_clash, word_effect_clash]
  constructor <;> ac_rfl

end Schwa
end PhonologicalRequirements
