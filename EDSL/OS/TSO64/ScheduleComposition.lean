/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.ScheduleTrace

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.OS.TSO64
open X86

/-- Compose two actual successful schedules at their common state, retaining
every action and observation under the same arbitrary profile and RMW family. -/
theorem schedule_append_of_success {before middle final : State}
    {left right : List Action} {leftObs rightObs : List Observation}
    {profile : Profile} {family : RMWFamily}
    (first : schedule before left profile family = .ok (middle, leftObs))
    (second : schedule middle right profile family = .ok (final, rightObs)) :
    schedule before (left ++ right) profile family =
      .ok (final, leftObs ++ rightObs) := by
  induction left generalizing before leftObs with
  | nil =>
    have same : (before, []) = (middle, leftObs) := Except.ok.inj first
    cases same
    exact second
  | cons action rest ih =>
    obtain ⟨head, tail, stepped, following, same⟩ := schedule_cons_ok first
    cases same
    have appended := ih following
    simp only [List.cons_append, schedule, stepped, ok_bind, appended, pure_ok]

end EDSL.OS.TSO64
