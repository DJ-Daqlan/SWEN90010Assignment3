-- Authors:
-- Yee Kiu Yeung - 1568135
-- Daqlan Lee - 1263658

-- Answer to Task 3.1.1:
-- Defining Position and Velocity as separate private types gives the program a
-- stronger type-level distinction between locations and rates of movement. Although
-- both are represented internally using Vector.Vector, client code cannot freely
-- substitute one for the other. Code must use the explicit conversion functions, such
-- as To_Position, To_Velocity, To_Vector, and Vel_To_Vector, whenever it really needs
-- to move between these concepts.
--
-- This prevents mistakes where a position is accidentally used as a velocity, or a
-- velocity is accidentally used as a position. For example, Spatial.Move has the type:
--
--       function Move (P : Position; V : Velocity) return Position;
--
-- If both arguments were plain Vector.Vector values, a call such as
-- Move (Velocity_As_Vector, Position_As_Vector) would compile even though the
-- arguments are conceptually reversed. With distinct Position and Velocity types, Ada
-- rejects that mistake at compile time. This also makes the code easier to read,
-- because the type of each value records whether it is being used as a position or as
-- a velocity.

-- Answer to Task 3.1.2:
-- Get_Position, Get_Velocity, and Get_Radius require Index to be between 1 and
-- Item_Count (U). The universe stores its items in a fixed array whose valid occupied
-- entries are exactly 1 .. Item_Count (U). Without these preconditions, a caller could
-- request an item at index 0 or at an index greater than the number of stored items,
-- causing an invalid array access.
--
-- Add_Item requires Item_Count (U) < Max_Items because the universe has a fixed-size
-- backing array. Adding an item when the universe is already full would increment the
-- count past the last valid array position and then try to write outside the array
-- bounds.
--
-- Reflect_Velocity_X and Reflect_Velocity_Y require Index to be between 1 and
-- Item_Count (U) for the same reason as the getter functions: they access and update
-- the item stored at that index. If the index did not refer to an existing item, the
-- procedure could read or write outside the valid occupied part of the array.

-- Answer to Task 3.7:
-- No, the proof does not guarantee that an early halt means a collision definitely
-- would have occurred in the full simulation. The collision check uses
-- Will_Collide_Vec on the current straight-line segment, using the relative position,
-- relative velocity, and squared sum of the radii. This proves that, if the current
-- velocities remain unchanged, the two straight-line trajectories will eventually
-- come within collision distance.
--
-- However, the full simulation also includes wall bounces. A bounce can occur before
-- the predicted collision point and change one or both velocities, producing a new
-- straight-line segment. Task 3.6 proves only the safe direction: when
-- No_Future_Collision_Pair is true, Lemma_No_Collision_Pair shows that the objects
-- are separated on the current frame for the current segment. It does not prove that
-- a predicted future collision is unavoidable in the full bouncing simulation.
-- Therefore, the simulation could halt conservatively even though no actual collision
-- would have happened after future bounces.

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

      if I = 1 then
         pragma Assert
           (Spatial.To_Vector (Univ.Get_Position (U, I)) =
            Vector.Add
              (Spatial.To_Vector (Initial_Positions (I)),
               Vector.Scale
                 (Spatial.Vel_To_Vector (Initial_Velocities (I)),
                  Tick_Count)));
      else
         pragma Assert (I = 2);
         pragma Assert
           (Spatial.To_Vector (Univ.Get_Position (U, I)) =
            Vector.Add
              (Spatial.To_Vector (Initial_Positions (I)),
               Vector.Scale
                 (Spatial.Vel_To_Vector (Initial_Velocities (I)),
                  Tick_Count)));
      end if;

      if J = 1 then
         pragma Assert
           (Spatial.To_Vector (Univ.Get_Position (U, J)) =
            Vector.Add
              (Spatial.To_Vector (Initial_Positions (J)),
               Vector.Scale
                 (Spatial.Vel_To_Vector (Initial_Velocities (J)),
                  Tick_Count)));
      else
         pragma Assert (J = 2);
         pragma Assert
           (Spatial.To_Vector (Univ.Get_Position (U, J)) =
            Vector.Add
              (Spatial.To_Vector (Initial_Positions (J)),
               Vector.Scale
                 (Spatial.Vel_To_Vector (Initial_Velocities (J)),
                  Tick_Count)));
      end if;
      pragma Assert (Univ.Get_Velocity (U, I) = Initial_Velocities (I));
      pragma Assert (Univ.Get_Velocity (U, J) = Initial_Velocities (J));

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

   Simulation_Loop :
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
      pragma Assert (Position_Invariant (U));

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
               exit Simulation_Loop;
            end if;
         end if;
      end;
   end loop Simulation_Loop;

   Disp.Capture (U);
   Disp.Save ("simulation.html",
              Arena_X_Min, Arena_X_Max,
              Arena_Y_Min, Arena_Y_Max);
   Ada.Text_IO.Put_Line ("Wrote simulation.html");
end Main;
