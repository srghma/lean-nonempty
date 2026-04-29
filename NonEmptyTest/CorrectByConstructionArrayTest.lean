import NonEmpty.CorrectByConstruction.Array

def test_non_empty_array_cbc () : IO Unit := do
  let a : NonEmptyArray Nat := #![1, 2, 3]
  let b : NonEmptyArray Nat := #![10]
  
  -- Test head and tail
  if a.head != 1 || a.tail != #[2, 3] then
    throw (IO.userError "head/tail failure")
  if b.head != 10 || b.tail != #[] then
    throw (IO.userError "singleton head/tail failure")

  -- Test size
  if a.size != 3 || b.size != 1 then
    throw (IO.userError "size failure")

  -- Test cons
  let c := NonEmptyArray.cons 0 a
  if c.head != 0 || c.tail != #[1, 2, 3] then
    throw (IO.userError "cons failure")

  -- Test singleton
  let d := NonEmptyArray.singleton 5
  if d.head != 5 || d.tail != #[] then
    throw (IO.userError "singleton failure")

  -- Test map
  let e := a.map (fun x => x + 1)
  if e.head != 2 || e.tail != #[3, 4] then
    throw (IO.userError "map failure")

  -- Test append
  let f := a.append b
  if f.head != 1 || f.tail != #[2, 3, 10] then
    throw (IO.userError "map failure")

  IO.println "CorrectByConstruction NonEmptyArray tests passed!"

def main : IO Unit := do
  test_non_empty_array_cbc
