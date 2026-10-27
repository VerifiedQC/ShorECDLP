import ShorECDLP.Submission.«2607_13816».Challenge.BatchedEndpoint
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Classical
noncomputable section
abbrev BatchWord := Fin 513 → Bool

def wordXor (a b : BatchWord) : BatchWord := fun i => xor (a i) (b i)
@[simp] theorem wordXor_zero (a : BatchWord) : wordXor a (fun _ => false) = a := by funext i; simp [wordXor]
@[simp] theorem wordXor_zero_left (a : BatchWord) : wordXor (fun _ => false) a = a := by funext i; simp [wordXor]
@[simp] theorem wordXor_self (a : BatchWord) : wordXor a a = (fun _ => false) := by funext i; simp [wordXor]

def batchLoad (e : Fin 8 → BatchWord) (sources : Bool) (target : Fin 4)
    (s : Fin 6 → BatchWord) : Fin 6 → BatchWord :=
  fun j => if h : j.val < 4 then
    if sources then wordXor (s j) (e ⟨j.val,by omega⟩) else s j
  else if j = 4 then wordXor (s j) (e ⟨4+target.val,by omega⟩) else s j

def batchSwap (source : Fin 4) (target : Fin 6) (s : Fin 6 → BatchWord) : Fin 6 → BatchWord :=
  Function.update s target (Equiv.swap (s ⟨source.val,by omega⟩) (s 4) (s target))

def batchInitial (data : BatchWord) : Fin 6 → BatchWord := fun j => if j=5 then data else fun _=>false

def batchModelStep (e : Fin 8 → BatchWord) (s : Fin 6 → BatchWord) : BatchOp → Fin 6 → BatchWord
  | .query sources target => batchLoad e sources target s
  | .swap source target => batchSwap source target s

def batchModel (e : Fin 8 → BatchWord) (s : Fin 6 → BatchWord) : Fin 6 → BatchWord :=
  batchSchedule.foldl (batchModelStep e) s

theorem batchModel_data (e : Fin 8 → BatchWord) (data : BatchWord) :
    batchModel e (batchInitial data) 5 =
      runFiniteSwaps (finiteMatchingSwaps [(e 0,e 4),(e 1,e 5),(e 2,e 6),(e 3,e 7)]) data := by
  simp [batchModel,batchSchedule,batchModelStep,batchInitial,batchLoad,batchSwap,Function.update,
    finiteMatchingSwaps,runFiniteSwaps,finiteMatchingPermutation]

theorem batchModel_clean (e : Fin 8 → BatchWord) (data : BatchWord) (j : Fin 6) (hj : j ≠ 5) :
    batchModel e (batchInitial data) j = fun _=>false := by
  fin_cases j <;> simp_all [batchModel,batchSchedule,batchModelStep,batchInitial,batchLoad,batchSwap,Function.update]
end
end ShorECDLP.Paper2607_13816.ChallengeMigration
