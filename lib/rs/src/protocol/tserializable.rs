use crate::protocol::{TInputProtocol, TOutputProtocol};
use crate::protocol::{TListIdentifier, TMapIdentifier, TSetIdentifier, TType};
use crate::OrderedFloat;
use crate::Result;
use std::collections::{BTreeMap, BTreeSet};
use std::convert::{From, TryFrom};

/// A trait for thrift serializable types. Any type implementing this trait can be read from a
/// `TInputProtocol` and written to a `TOuputprotocol`.
///
/// The trait can also be derived for structs and enums via a derive macro
pub trait TSerializable {
    /// Returns the thrift struct-field type corresponding to the type
    fn get_ttype() -> TType;
    /// Reads a value from a input protocol
    fn read_from_in_protocol(i_prot: &mut dyn TInputProtocol) -> Result<Box<Self>>;
    /// Writes a value to an output protocol
    fn write_to_out_protocol(&self, o_prot: &mut dyn TOutputProtocol) -> Result<()>;
}

// A simple macro to expand the implementation of TSerializable for simple types
macro_rules! tserializable_impl {
    ($base_type: ty, $ttype: expr, $read_f: ident, $write_f: ident) => {
        impl TSerializable for $base_type {
            fn get_ttype() -> TType {
                $ttype
            }
            fn read_from_in_protocol(i_prot: &mut dyn TInputProtocol) -> Result<Box<Self>> {
                i_prot.$read_f().map(Box::new)
            }
            fn write_to_out_protocol(&self, o_prot: &mut dyn TOutputProtocol) -> Result<()> {
                o_prot.$write_f(*self)
            }
        }
    };
}

// Trait implementation for base types

tserializable_impl!(bool, TType::Bool, read_bool, write_bool);
tserializable_impl!(i8, TType::I08, read_i8, write_i8);
tserializable_impl!(i16, TType::I16, read_i16, write_i16);
tserializable_impl!(i32, TType::I32, read_i32, write_i32);
tserializable_impl!(i64, TType::I64, read_i64, write_i64);
tserializable_impl!(f64, TType::Double, read_double, write_double);

impl TSerializable for OrderedFloat<f64> {
    fn get_ttype() -> TType {
        TType::Double
    }
    fn read_from_in_protocol(i_prot: &mut dyn TInputProtocol) -> Result<Box<Self>> {
        i_prot.read_double().map(OrderedFloat::from).map(Box::new)
    }
    fn write_to_out_protocol(&self, o_prot: &mut dyn TOutputProtocol) -> Result<()> {
        o_prot.write_double(self.into_inner())
    }
}

impl TSerializable for String {
    fn get_ttype() -> TType {
        TType::String
    }
    fn read_from_in_protocol(i_prot: &mut dyn TInputProtocol) -> Result<Box<Self>> {
        i_prot.read_string().map(Box::new)
    }
    fn write_to_out_protocol(&self, o_prot: &mut dyn TOutputProtocol) -> Result<()> {
        o_prot.write_string(self)
    }
}

impl TSerializable for Vec<u8> {
    fn get_ttype() -> TType {
        TType::List
    }
    fn read_from_in_protocol(i_prot: &mut dyn TInputProtocol) -> Result<Box<Self>> {
        i_prot.read_bytes().map(|v| Box::new(v))
    }
    fn write_to_out_protocol(&self, o_prot: &mut dyn TOutputProtocol) -> Result<()> {
        o_prot.write_bytes(self)
    }
}

// Trait implementation for composite types

// Map (BTreeMap)
impl<K, I> TSerializable for BTreeMap<K, I>
where
    K: TSerializable + std::cmp::Ord,
    I: TSerializable,
{
    fn get_ttype() -> TType {
        TType::Map
    }
    fn read_from_in_protocol(i_prot: &mut dyn TInputProtocol) -> Result<Box<Self>> {
        let map_stone = i_prot.read_map_begin()?;
        let mut map = Box::new(BTreeMap::new());
        for _ in 0..map_stone.size {
            let map_key = K::read_from_in_protocol(i_prot)?;
            let map_item = I::read_from_in_protocol(i_prot)?;
            map.insert(*map_key, *map_item);
        }
        Result::Ok(map)
    }
    fn write_to_out_protocol(&self, o_prot: &mut dyn TOutputProtocol) -> Result<()> {
        o_prot.write_map_begin(&TMapIdentifier::new(
            K::get_ttype(),
            I::get_ttype(),
            self.len() as i32,
        ))?;
        for (key, val) in self {
            key.write_to_out_protocol(o_prot)?;
            val.write_to_out_protocol(o_prot)?;
            o_prot.write_map_end()?;
        }
        Result::Ok(())
    }
}

// List (Vec)
impl<K> TSerializable for Vec<K>
where
    K: TSerializable,
{
    fn get_ttype() -> TType {
        TType::List
    }
    fn read_from_in_protocol(i_prot: &mut dyn TInputProtocol) -> Result<Box<Self>> {
        let list_stone = i_prot.read_list_begin()?;
        let mut val: Vec<K> = Vec::with_capacity(list_stone.size as usize);
        for _ in 0..list_stone.size {
            let list_elem = K::read_from_in_protocol(i_prot)?;
            val.push(*list_elem);
        }
        Result::Ok(Box::new(val))
    }
    fn write_to_out_protocol(&self, o_prot: &mut dyn TOutputProtocol) -> Result<()> {
        o_prot.write_list_begin(&TListIdentifier::new(K::get_ttype(), self.len() as i32))?;
        for elem in self {
            elem.write_to_out_protocol(o_prot)?;
            o_prot.write_list_end()?;
        }
        Result::Ok(())
    }
}

// Set (BTreeSet)
impl<K> TSerializable for BTreeSet<K>
where
    K: TSerializable + std::cmp::Ord,
{
    fn get_ttype() -> TType {
        TType::Set
    }
    fn read_from_in_protocol(i_prot: &mut dyn TInputProtocol) -> Result<Box<Self>> {
        let set_stone = i_prot.read_set_begin()?;
        let mut val = BTreeSet::new();
        for _ in 0..set_stone.size {
            let set_elem = K::read_from_in_protocol(i_prot)?;
            val.insert(*set_elem);
        }
        Result::Ok(Box::new(val))
    }
    fn write_to_out_protocol(&self, o_prot: &mut dyn TOutputProtocol) -> Result<()> {
        o_prot.write_set_begin(&TSetIdentifier::new(K::get_ttype(), self.len() as i32))?;
        for elem in self {
            elem.write_to_out_protocol(o_prot)?;
            o_prot.write_set_end()?;
        }
        Result::Ok(())
    }
}

// Option
impl<K: TSerializable> TSerializable for std::option::Option<K> {
    fn get_ttype() -> TType {
        K::get_ttype()
    }
    fn read_from_in_protocol(i_prot: &mut dyn TInputProtocol) -> Result<Box<Self>> {
        let inner_val = K::read_from_in_protocol(i_prot)?;
        Result::Ok(Box::new(Some(*inner_val)))
    }
    fn write_to_out_protocol(&self, o_prot: &mut dyn TOutputProtocol) -> Result<()> {
        match self {
            Some(val) => val.write_to_out_protocol(o_prot),
            None => Result::Ok(()),
        }
    }
}

// Box

impl<K: TSerializable> TSerializable for Box<K> {
    fn get_ttype() -> TType {
        K::get_ttype()
    }
    fn read_from_in_protocol(i_prot: &mut dyn TInputProtocol) -> Result<Box<Self>> {
        let inner_val = K::read_from_in_protocol(i_prot)?;
        Result::Ok(Box::new(inner_val))
    }
    fn write_to_out_protocol(&self, o_prot: &mut dyn TOutputProtocol) -> Result<()> {
        (**self).write_to_out_protocol(o_prot)
    }
}
