with Ada.Text_IO; with Ada.Integer_Text_IO;

package body Universe with SPARK_Mode is

   procedure Init (U : out Universe) is
   begin
      --  TODO: implement
      U.item_count := 0;
      U.items := (others => <>); -- Default empty Universe_Item

      --raise Program_Error with "Init not yet implemented";
   end Init;

   procedure Add_Item
     (U   : in out Universe;
      pos : Spatial.Position;
      vel : Spatial.Velocity;
      rad : Big_Real)
   is
   begin
      --  TODO: implement

      -- Since it's a base-one index, the 
      -- first increment will go from 0 -> 1
      U.item_count := U.item_count + 1;
      U.items(U.item_count) := ( 
         pos => pos,
         vel => vel,
         rad => rad
      );
      --raise Program_Error with "Add_Item not yet implemented";
   end Add_Item;

   procedure Reflect_Velocity_X
     (U : in out Universe; Index : Integer) is
   begin
      --  TODO: implement
      U.items(Index).vel := Spatial.Negate_Vel_X(V => U.items(Index).vel);
      -- raise Program_Error with "Reflect_Velocity_X not yet implemented";
   end Reflect_Velocity_X;

   procedure Reflect_Velocity_Y
     (U : in out Universe; Index : Integer) is
   begin
      --  TODO: implement
      U.items(Index).vel := Spatial.Negate_Vel_Y (V => U.items(Index).vel);
      -- raise Program_Error with "Reflect_Velocity_Y not yet implemented";
   end Reflect_Velocity_Y;

   procedure Print (U : Universe)
     with SPARK_Mode => Off
   is
   begin
      for I in U.items'First .. U.item_count loop
         Ada.Text_IO.Put ("Item: ");
         Ada.Integer_Text_IO.Put (I);
         Ada.Text_IO.Put (": pos: (");
         Ada.Text_IO.Put
           (To_String (Spatial.Pos_X (U.items (I).pos)));
         Ada.Text_IO.Put (",");
         Ada.Text_IO.Put
           (To_String (Spatial.Pos_Y (U.items (I).pos)));
         Ada.Text_IO.Put (")");
         Ada.Text_IO.New_Line;
      end loop;
   end Print;

   procedure Tick (U : in out Universe) is
   begin
      --  TODO: implement
      for ItemIndex in 1 .. U.item_count loop
         pragma Loop_Invariant (U.item_count = U'Loop_Entry.item_count);
         pragma Loop_Invariant
           (for all I in 1 .. U.item_count =>
              U.items (I).vel = U'Loop_Entry.items (I).vel
              and then U.items (I).rad = U'Loop_Entry.items (I).rad);
         pragma Loop_Invariant
           (for all I in 1 .. ItemIndex - 1 =>
              U.items (I).pos =
                Spatial.Move (U'Loop_Entry.items (I).pos,
                              U'Loop_Entry.items (I).vel));
         pragma Loop_Invariant
           (for all I in ItemIndex .. U.item_count =>
              U.items (I).pos = U'Loop_Entry.items (I).pos);

         U.items (ItemIndex).pos :=
           Spatial.Move (P => U.items (ItemIndex).pos,
                         V => U.items (ItemIndex).vel);
      end loop;

      --raise Program_Error with "Tick not yet implemented";
   end Tick;

end Universe;
