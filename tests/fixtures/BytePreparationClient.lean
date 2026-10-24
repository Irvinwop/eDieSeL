/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.State

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Synthetic client declarations, kept out of the trusted replay snapshot.
Observed test bytes deliberately differ from this original source. -/
namespace BytePreparationFixture
open EDSL

def original : List X86.Byte := [41, 42, 43, 44, 45, 46]
def file : List X86.Byte := original

def first : List X86.Byte := file.take 2
def second : List X86.Byte := (file.drop 2).take 2
def third : List X86.Byte := (file.drop 4).take 2
def assembled : List X86.Byte := first ++ second ++ third

theorem root : assembled = file := Eq.refl assembled

-- Together with root, these lengths fix the ordered intervals, including a
-- partial final chunk, even if a producer preserves only the complete join.
theorem partitionLengths : first.length = 2 ∧ second.length = 2 ∧
    third.length = file.length - 4 := by decide +kernel

def wideFile : List X86.Byte :=
  [41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60]
def wideFirst : List X86.Byte := wideFile.take 17
def wideLast : List X86.Byte := (wideFile.drop 17).take 17

theorem wideRoot : wideFirst ++ wideLast = wideFile := Eq.refl (wideFirst ++ wideLast)
theorem wideLengths : wideFirst.length = 17 ∧ wideLast.length = wideFile.length - 17 := by
  decide +kernel

def emptyFile : List X86.Byte := []
theorem emptyRoot : emptyFile = emptyFile := Eq.refl emptyFile

def oneFile : List X86.Byte := [42]
def oneChunk : List X86.Byte := oneFile.take 2
theorem oneRoot : oneChunk = oneFile := Eq.refl oneChunk

end BytePreparationFixture
