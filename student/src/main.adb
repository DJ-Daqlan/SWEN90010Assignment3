-- Answer to Task 3.1.1: 
-- Defining Position and Velocity as private types with expression functions has multiple
-- advantages. First, Ada prevents implicit widening/narrowing-style conversions between
-- Velocity and Position and Vector.Vector, because Position and Velocity are distinct
-- derived types. The code must use explicit conversion functions, so accidental mixing of
-- positions, velocities, and raw vectors is caught by the compiler. Second, it provides a
-- better API design. It allows the SPARK prover to reason about them effectively, while
-- still providing a clear interface for the rest of the code. Other functions such as Move,
-- Negate_Vel_X, and Negate_Vel_Y are defined in terms of the underlying vector operations,
-- but the prover can still understand their behavior through the expression functions.
-- Third, it prevents it from accidentally compile while mixing up Position and Velocity,
-- i.e. if they were not distinct types and just Vector.Vector, they are interchangeable,
-- and the prover would not be able to catch mistakes where a Position is used where a
-- Velocity is expected, or vice versa. Fourth, it more human readable, as it makes it clear
-- when we are working with positions versus velocities, which can help prevent bugs and
-- improve code clarity.
-- 
-- This design can prevent certain programming errors, such as accidentally using a velocity
-- where a position is expected, and vice versa. For example, the Move function takes a Position
-- and a Velocity and returns a new Position:
--       function Move (P : Position; V : Velocity) return Position;
-- If Position and Velocity were just aliases for Vector.Vector, it would accidentally compile
-- if we passed a Velocity where a Position is expected, or vice versa:
--       Move (Velocity_As_Vector, Position_As_Vector)
-- Also, you may store a Velocity in a variable that is intended to hold a Position, and the
-- compiler would not catch this mistake. By defining Position and Velocity as distinct types,
-- the compiler can catch these kinds of errors at compile time, which can help prevent bugs
-- and improve code safety.

-- Answer to Task 3.1.2: 
-- Add_Item: Pre => Item_Count (U) < Max_Items
-- Add_Item has a preconditon to check if the number of existing items in the universe is less
-- than the maximum allowed items. This is important because the universe has a fixed-size array
-- to store items, and if we try to add more items than the maximum, SPARK Prover can help us
-- catch this error at compile time. If this precondition is removed, it would allow the possibility
-- of adding more items than the maximum limit, which could lead to a runtime error due to array
-- bounds violation when trying to add items beyond the maximum limit.
-- 
-- Reflect_Velocity_X: Pre => Index >= 1 and then Index <= Item_Count (U)
-- Reflect_Velocity_X has a precondition to ensure that the index provided is within the valid range.
-- Since the items in the universe are stored in a base-one indexed array, the valid indices are from 1
-- to Item_Count (U). This precondition ensures that we do not access the items array out of bounds.
-- If we remove this precondition, it would lead to a runtime error due to array bounds violation when
-- trying to access the items array with an invalid index (e.g., 0 or greater than Item_Count (U)).
--
-- Reflect_Velocity_Y: Pre => Index >= 1 and then Index <= Item_Count (U)
-- Reflect_Velocity_Y has the same precondition as Reflect_Velocity_X for the same reason. It checks if
-- the index provided is within the valid range of 1 to Item_Count (U) to prevent out-of-bounds access
-- when accessing the items array. If this precondition is removed, it could lead to runtime errors
-- caused by array bounds violation if an invalid index is used.

-- Answer to Task 3.7:
-- The proof does not guarantee that an actual collision definitely would have occurred had the simulation
-- continued whenever the simulation halts early. The check No_Future_Collision_Pair uses
-- Will_Collide_Vec(S, V, Eps2), where S is the difference between the two initial positions after the
-- most recent reset/bounce, V is the difference between their velocities, and Eps2 is the squared sum
-- of their radii. This predicts whether the relative straight-line trajectory S + tV ever comes within
-- collision distance, assuming the current velocities remain constant.
-- 
-- Task 3.6 only asks us to prove soundness for the current straight-line segment between bounces, not to
-- predict all later segments after future wall reflections. Therefore the proof does not need to model
-- every possible future bounce before deciding whether the early halt is a true unavoidable collision.
-- The Task 3.6 proof only establishes the safe direction: if No_Future_Collision_Pair is true, then
-- Lemma_No_Collision_Pair proves that the objects are not colliding on the current settings (positions
-- and velosities) and predicted trajectories. It does not prove that a predicted future collision must
-- occur in actual simulations, where wall reflections are considered. Since the real simulation includes
-- future wall reflections, a bounce could change the velocities before the predicted collision point, so
-- the simulation could halt conservatively even though no actual collision would have happened.


with Collision_Math;
with Universe;
with Spatial;
with Vector; use Vector;
with Display;
with Ada.Text_IO;
with Ada.Numerics.Big_Numbers.Big_Reals;
use Ada.Numerics.Big_Numbers.Big_Reals;

procedure Main with SPARK_Mode is
   use type Spatial.Velocity;
   package Univ is new Universe (10);

   package FC is new Float_Conversions (Float);
   package Disp is new Display (Univ, Max_Frames => 5500);

   U : Univ.Universe;

   Arena_X_Min : constant Big_Real := FC.To_Big_Real (-100.0);
   Arena_X_Max : constant Big_Real := FC.To_Big_Real (100.0);
   Arena_Y_Min : constant Big_Real := FC.To_Big_Real (-50.0);
   Arena_Y_Max : constant Big_Real := FC.To_Big_Real (50.0);

   Initial_Positions : array (1 .. 2) of Spatial.Position :=
     (Spatial.To_Position
        ((X => FC.To_Big_Real (0.0), Y => FC.To_Big_Real (5.0))),
      Spatial.To_Position
        ((X => FC.To_Big_Real (0.0), Y => FC.To_Big_Real (-5.0))));

   Initial_Velocities : array (1 .. 2) of Spatial.Velocity :=
     (Spatial.To_Velocity
        ((X => FC.To_Big_Real (0.4), Y => FC.To_Big_Real (0.3))),
      Spatial.To_Velocity
        ((X => FC.To_Big_Real (1.0), Y => FC.To_Big_Real (-0.7))));

   Initial_Radii : constant array (1 .. 2) of Big_Real :=
     (FC.To_Big_Real (2.0), FC.To_Big_Real (2.0));

   Tick_Count : Big_Real := To_Big_Real (0);

   --  TODO: define Position_Invariant
   function Position_Invariant
     (U : Univ.Universe) return Boolean
   is
     (Univ.Item_Count (U) = 2
      and then Tick_Count >= To_Big_Real (0)
      -- Position of Item 1
      and then Spatial.Pos_X (Univ.Get_Position (U, 1)) =
        Spatial.Pos_X (Initial_Positions (1))
        + Tick_Count * Spatial.Vel_To_Vector (Initial_Velocities (1)).X
      and then Spatial.Pos_Y (Univ.Get_Position (U, 1)) =
        Spatial.Pos_Y (Initial_Positions (1))
        + Tick_Count * Spatial.Vel_To_Vector (Initial_Velocities (1)).Y
      -- Position of Item 2
      and then Spatial.Pos_X (Univ.Get_Position (U, 2)) =
        Spatial.Pos_X (Initial_Positions (2))
        + Tick_Count * Spatial.Vel_To_Vector (Initial_Velocities (2)).X
      and then Spatial.Pos_Y (Univ.Get_Position (U, 2)) =
        Spatial.Pos_Y (Initial_Positions (2))
        + Tick_Count * Spatial.Vel_To_Vector (Initial_Velocities (2)).Y
      -- Constant variables remain constant
      and then Univ.Get_Velocity (U, 1) = Initial_Velocities (1)
      and then Univ.Get_Velocity (U, 2) = Initial_Velocities (2)
      and then Univ.Get_Radius (U, 1) = Initial_Radii (1)
      and then Univ.Get_Radius (U, 2) = Initial_Radii (2));

   function Squared_Dist
     (U : Univ.Universe; I, J : Integer) return Big_Real is
       (Vector.Dot
          (Vector.Sub
             (Spatial.To_Vector (Univ.Get_Position (U, I)),
              Spatial.To_Vector (Univ.Get_Position (U, J))),
           Vector.Sub
             (Spatial.To_Vector (Univ.Get_Position (U, I)),
              Spatial.To_Vector (Univ.Get_Position (U, J))))) with
      Pre => I >= 1 and then I <= Univ.Item_Count (U)
             and then J >= 1 and then J <= Univ.Item_Count (U);

   function Pair_Sep2
     (I, J : Integer) return Big_Real is
       ((Initial_Radii (I) + Initial_Radii (J)) *
        (Initial_Radii (I) + Initial_Radii (J))) with
      Pre => I in 1 .. 2 and J in 1 .. 2;

   --  TODO: define No_Future_Collision_Pair
   function No_Future_Collision_Pair
      (I, J : Integer) return Boolean is
         (not (Collision_Math.Will_Collide_Vec (
            S => Vector.Sub (
               V1 => Spatial.To_Vector (Initial_Positions (I)), 
               V2 => Spatial.To_Vector (Initial_Positions (J))
            ), 
            V => Vector.Sub (
               V1 => Spatial.Vel_To_Vector (Initial_Velocities (I)), 
               V2 => Spatial.Vel_To_Vector (Initial_Velocities (J))
            ), 
            Eps2 => Pair_Sep2 (I => I, J => J)
            )))
      with 
         Pre => I in 1 .. 2 and J in 1 .. 2;

   --  TODO: define Lemma_No_Collision_Pair
   procedure Lemma_No_Collision_Pair
   (U : Univ.Universe; I, J : Integer)
   with
      Ghost,
      Pre => (
         Position_Invariant (U) and then
         I in 1 .. 2 and then
         J in 1 .. 2 and then
         Tick_Count >= To_Big_Real (0) and then
         No_Future_Collision_Pair (I, J)
      ),
      Post => (
         Squared_Dist (U => U, I => I, J => J) > Pair_Sep2 (I => I, J => J)
      )
   is 
   begin
      Collision_Math.Check_Implies_Safe_Vec (
         S => Vector.Sub (
            V1 => Spatial.To_Vector (P => Initial_Positions (I)),
            V2 => Spatial.To_Vector (P => Initial_Positions (J))
         ), 
         V => Vector.Sub (
            V1 => Spatial.Vel_To_Vector (V => Initial_Velocities (I)), 
            V2 => Spatial.Vel_To_Vector (V => Initial_Velocities (J))
         ),
         Eps2 => Pair_Sep2 (I => I, J => J), 
         T => Tick_Count);

      Collision_Math.Lemma_Sq_Dist_Bridge (
         P1 => Spatial.To_Vector (P => Univ.Get_Position (U => U, Index => I)), 
         P2 => Spatial.To_Vector (P => Univ.Get_Position (U => U, Index => J)), 
         Init1 => Spatial.To_Vector (P => Initial_Positions (I)), 
         Init2 => Spatial.To_Vector (P => Initial_Positions (J)), 
         Vel1 => Spatial.Vel_To_Vector (V => Univ.Get_Velocity (U => U, Index => I)), 
         Vel2 => Spatial.Vel_To_Vector (V => Univ.Get_Velocity (U => U, Index => J)), 
         T => Tick_Count);
   end Lemma_No_Collision_Pair;

   type Bounce_Flags is record
      X : Boolean := False;
      Y : Boolean := False;
   end record;

   type Bounce_Array is array (1 .. 2) of Bounce_Flags;

   function Detect_Bounces
     (U : Univ.Universe) return Bounce_Array
     with Pre => Univ.Item_Count (U) = 2;

   function Detect_Bounces
     (U : Univ.Universe) return Bounce_Array
   is
      Result : Bounce_Array := (others => (X => False, Y => False));
   begin
      for Item in 1 .. 2 loop
         declare
            P : constant Spatial.Position :=
              Univ.Get_Position (U, Item);
            R : constant Big_Real := Univ.Get_Radius (U, Item);
         begin
            if Spatial.Pos_X (P) + R > Arena_X_Max
              or else Spatial.Pos_X (P) - R < Arena_X_Min
            then
               Result (Item).X := True;
            end if;
            if Spatial.Pos_Y (P) + R > Arena_Y_Max
              or else Spatial.Pos_Y (P) - R < Arena_Y_Min
            then
               Result (Item).Y := True;
            end if;
         end;
      end loop;
      return Result;
   end Detect_Bounces;

   procedure Print_Collision (Frame : Integer);

   procedure Print_Collision (Frame : Integer)
     with SPARK_Mode => Off
   is
   begin
      Ada.Text_IO.Put_Line
        ("Collision will occur after bounce at frame"
         & Integer'Image (Frame));
      for Item in 1 .. 2 loop
         declare
            V : constant Vector.Vector :=
              Spatial.Vel_To_Vector (Initial_Velocities (Item));
            P : constant Spatial.Position :=
              Initial_Positions (Item);
         begin
            Ada.Text_IO.Put_Line
              ("  Item" & Integer'Image (Item)
               & " pos=("
               & To_String (Spatial.Pos_X (P)) & ", "
               & To_String (Spatial.Pos_Y (P)) & ")"
               & " vel=("
               & To_String (V.X) & ", "
               & To_String (V.Y) & ")");
         end;
      end loop;
      Ada.Text_IO.Put_Line
        ("  Sep2=" & To_String (Pair_Sep2 (1, 2)));
   end Print_Collision;

   procedure Reset_Universe
   --  TODO: add postcondition
   with Post => Position_Invariant (U)
   is
   begin
      Tick_Count := To_Big_Real (0);
      Univ.Init (U);
      Univ.Add_Item (U,
                     Initial_Positions (1),
                     Initial_Velocities (1),
                     Initial_Radii (1));
      Univ.Add_Item (U,
                     Initial_Positions (2),
                     Initial_Velocities (2),
                     Initial_Radii (2));
   end Reset_Universe;

begin
   Reset_Universe;

   --  TODO: add pre-loop collision check
   if not No_Future_Collision_Pair (1, 2) then
      Print_Collision (0);
      exit;
   end if;

   for Frame in 1 .. 5000 loop
      --  TODO: add loop invariants
      pragma Loop_Invariant (Position_Invariant (U));
      pragma Loop_Invariant (No_Future_Collision_Pair (1, 2));

      --  TODO: call soundness lemma and assert collision freedom
      Lemma_No_Collision_Pair (U => U, I => 1, J => 2);
      pragma Assert (Squared_Dist (U => U, I => 1, J => 2) > Pair_Sep2 (I => 1, J => 2));

      Disp.Capture (U);
      Univ.Tick (U);
      Tick_Count := Tick_Count + To_Big_Real (1);

      declare
         Flags : constant Bounce_Array := Detect_Bounces (U);
      begin
         if Flags (1).X or else Flags (1).Y
           or else Flags (2).X or else Flags (2).Y
         then
            for Item in 1 .. 2 loop
               pragma Loop_Invariant (Univ.Item_Count (U) = 2);
               if Flags (Item).X then
                  Univ.Reflect_Velocity_X (U, Item);
               end if;
               if Flags (Item).Y then
                  Univ.Reflect_Velocity_Y (U, Item);
               end if;
            end loop;
            Initial_Positions :=
              (Univ.Get_Position (U, 1),
               Univ.Get_Position (U, 2));
            Initial_Velocities :=
              (Univ.Get_Velocity (U, 1),
               Univ.Get_Velocity (U, 2));

            Reset_Universe;

            --  TODO: add post-bounce collision check
            if not No_Future_Collision_Pair (1, 2) then
               Print_Collision (Frame);
               exit;
            end if;
         end if;
      end;
   end loop;

   Disp.Capture (U);
   Disp.Save ("simulation.html",
              Arena_X_Min, Arena_X_Max,
              Arena_Y_Min, Arena_Y_Max);
   Ada.Text_IO.Put_Line ("Wrote simulation.html");
end Main;
