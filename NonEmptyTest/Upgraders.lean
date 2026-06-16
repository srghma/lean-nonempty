import NonEmpty

open NonEmpty.Aliases
open NonEmpty.List.FilterMap
open NonEmpty.List.Traverse

-- FilterMap lax test
def testFilterMap : «L/NES» := NonEmpty.List.FilterMap.«L/S->L/NES» ["hello", "", "world"]
#guard testFilterMap.length == 2

-- Traverse strict test
def testTraverse1 : Option «L/NES» := NonEmpty.List.Traverse.«L/S->L/NES» ["hello", "", "world"]
#guard testTraverse1 == none

def testTraverse2 : Option «L/NES» := NonEmpty.List.Traverse.«L/S->L/NES» ["hello", "world"]
#guard testTraverse2.isSome == true
