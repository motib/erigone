-- Copyright 2008-12 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Text_IO;
with Ada.Unchecked_Conversion;
with Global; use Global;
with Automata, Options, State_Vectors, Symbol_Tables, Utilities;
package body Compress_Vectors.Hash_Tables is

  -- The hash table can have up to 2**32 slots
  type Hash_Type is mod 2**32;
  -- The actual number of slots (see procedure Initialize)
  Hash_Slots: Hash_Type;

  -- Buckets for hash elements
  type Hash_Element;
  type Hash_Access is access all Hash_Element;
  type Hash_Element is
    record
      Next:    Hash_Access;
      Element: Compressed_Vector;
    end record;

  -- The hash table is an array of pointers to buckets
  -- Its size can be set by an argument, so table is an access type
  type Hash_Array is array(Hash_Type range <>) of Hash_Access;
  Hash_Table: access Hash_Array;

  Stored_Elements:  Natural;  -- Count of stored elements
  Matched_Elements: Natural;  -- Count of matched elements
  Collisions:       Natural;  -- Count of hash table collisions

  procedure Initialize is
  begin
    Stored_Elements  := 0;
    Matched_Elements := 0;
    Collisions       := 0;
    Hash_Slots       := Hash_Type(2**Options.Hash_Slots);
    Hash_Table       := new Hash_Array(Hash_Type range 0..Hash_Slots-1);
  end Initialize;

  -- Hash function FNV 1a
  --   http://isthe.com/chongo/tech/comp/fnv/
  function Hash(Element: Compressed_Vector) return Hash_Type is
    use type Options.Execution_Type;
    H: Hash_Type;
  begin
    H := 2166136261;
    for I in 0..Automata.Processes-1 loop
      H := H xor Hash_Type(Element.Process(I));
      H := H * 16777619;
    end loop;
    for I in 0..Symbol_Tables.Variables-1 loop
      H := H xor Hash_Type(Element.Variable(I));
      H := H * 16777619;
    end loop;
    -- For acceptance/fairness, include inner flag
    -- For fairness, include fair counter
    if Options.Execution_Mode /= Options.Safety then
      H := H xor Hash_Type(Element.Inner);
      if Options.Execution_Mode = Options.Fairness then
        H := H * 16777619;
        H := H xor Hash_Type(Element.Fair);
      end if;
    end if;
    -- xor folding for size of hash table
    H := (H / Hash_Slots) xor (H mod Hash_Slots);
    return H;
  end Hash;

  -- Put the state vector S in the hash table,
  --   return if it was Inserted or not (because it was already there)
  procedure Put_State(
      S:        in State_Vectors.State_Vector;
      Inserted: out Boolean) is

    -- Compress the state vector before putting in hash table
    CV: Compressed_Vector := Compress_Vectors.Compress(S);
    -- Compute the hash value of the vector
    H:  Hash_Type := Hash(CV);
    -- Variable for traversing chain of buckets
    P:  Hash_Access;
  begin
    -- If hash table entry is null, insert the first bucket
    if Hash_Table(H) = null then
      Hash_Table(H) := new Hash_Element'(null, CV);
      Stored_Elements  := Stored_Elements  + 1;
      Inserted := True;
    else
      -- Hash table entry contains a pointer to a list of buckets
      P := Hash_Table(H);
      loop
        -- If a bucket contains this vector, it is matched
        if P.Element = CV then
          Matched_Elements := Matched_Elements + 1;
          Inserted := False;
          exit;
        -- If not matched by end of chain, this is a collision
        --   Store the new vector at the end of the chain
        elsif P.Next = null then
          P.Next := new Hash_Element'(null, CV);
          Collisions := Collisions + 1;
          Stored_Elements  := Stored_Elements  + 1;
          Inserted := True;
          exit;
        -- Next bucket in the chain
        else
          P := P.Next;
        end if;
      end loop;
    end if;

    if Options.Display(Options.Hash) then
      Utilities.Put("inserted=", Inserted);
      State_Vectors.Put_State_Vector("", S);
    end if;
  end Put_State;

  -- Put hash table statistics at end of execution
  -- First line is state vector statistics and number of collisions
  -- Second line is the memory used
  --   The overhead is one pointer for each hash table entry
  --     plus one pointer for each element stored
  procedure Put_Hash is
    S: Natural := Compress_Vectors.Compressed_Vector'Size;
    E: Natural := Integer(S/Byte'Size);
    use Utilities;
  begin
    Put("states stored=", Long_Integer(Stored_Elements));
    Put("matched=",       Long_Integer(Matched_Elements));
    Put("total=",         Long_Integer(Stored_Elements + Matched_Elements));
    Put("collisions=",    Long_Integer(Collisions), New_Line => True);

    Put("element size=",  E);
    Put("memory=",        Long_Integer(Stored_Elements*E));
    Put("overhead=",      Long_Integer(Positive(Hash_Slots) * 
                                   (Hash_Access'Size/Byte'Size) +
                          Stored_Elements * (Hash_Access'Size/Byte'Size)),
                          New_Line => True);
  end Put_Hash;
end Compress_Vectors.Hash_Tables;
