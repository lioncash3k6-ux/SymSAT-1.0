import MonsterVerified.Checker
open MonsterVerified
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def R33_le_6_kernel_steps : List Step := [
  .add 41 [(-4 : Int), (-2 : Int), (-1 : Int)] [1, 2, 5, 31],
  .add 42 [(-1 : Int), (-2 : Int), (-4 : Int)] [41],
  .img 43 41 #[0, 3, 1, 2, 4, 5] true,
  .img 44 41 #[0, 4, 1, 2, 3, 5] true,
  .img 45 41 #[0, 5, 1, 2, 3, 4] true,
  .add 46 [(2 : Int), (1 : Int)] [43, 44, 8, 45, 9, 10, 40],
  .img 47 46 #[0, 3, 2, 1, 4, 5] true,
  .img 48 46 #[0, 4, 2, 1, 3, 5] true,
  .add 49 [(1 : Int)] [46, 47, 22, 48, 23, 28, 14],
  .img 50 46 #[0, 2, 1, 3, 4, 5] true,
  .add 51 [(-2 : Int)] [49, 50],
  .img 52 46 #[0, 3, 1, 2, 4, 5] true,
  .add 53 [(-4 : Int)] [49, 52],
  .add 54 [(6 : Int)] [53, 51, 25],
  .img 55 46 #[0, 4, 1, 2, 3, 5] true,
  .add 56 [(-7 : Int)] [49, 55],
  .add 57 [(9 : Int)] [56, 51, 26],
  .add 58 [(10 : Int)] [56, 53, 28],
  .add 59 [] [58, 57, 54, 17]]

/-- kernel-checked: no compiler trust -/
theorem R33_le_6_kernel : ∀ c, ¬ Good 3 3 6 c :=
  check_sound (steps := R33_le_6_kernel_steps) (by decide +kernel)

