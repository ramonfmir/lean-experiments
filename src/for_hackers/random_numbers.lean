import system.io

open char
open list
open io
open ordering

def rand_range (lo : nat) (hi : nat) : io nat := do
  r ← io.cmd { cmd := "head", args := ["-c 80", "/dev/urandom"] },
  let seed         := foldl (+) 0 $ map to_nat r.to_list,
  let gen          := mk_std_gen seed,
  let (target, _)  := rand_nat gen lo hi,
  return target

def get_guess : io nat := do
  put_str "Guess a number: ",
  response ← get_line,
  return $ string.to_nat response

def main : io unit := do
  put_str "Guess a number between 1 and 100 (inclusive)",
  target ← rand_range 1 100,
  iterate 20 $ λ i,
    if i > 0 then do {
      put_str $ "You have " ++ (to_string i) ++ " guesses.\n",
      guess ← get_guess,
      match cmp guess target with
      | eq := do { put_str "You won!\n", return none }
      | gt := do { put_str "Too high!\n", return $ some (i - 1) }
      | lt := do { put_str "Too low!\n", return $ some (i - 1) }
      end
    }
    else
      return none,
 return ()
 