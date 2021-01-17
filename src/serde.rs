use crate::TsilCev;
use core::marker::PhantomData;
use serde::{
    de::{Deserialize, Deserializer, SeqAccess, Visitor},
    ser::{Serialize, SerializeSeq, Serializer},
};

impl<T: Serialize> Serialize for TsilCev<T> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut state = serializer.serialize_seq(Some(self.len()))?;
        for item in self.iter_tsil() {
            state.serialize_element(&item)?;
        }
        state.end()
    }
}

impl<'de, T: Deserialize<'de>> Deserialize<'de> for TsilCev<T> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_seq(TsilCevVisitor {
            phantom: PhantomData,
        })
    }
}

struct TsilCevVisitor<T> {
    phantom: PhantomData<T>,
}

impl<'de, T: Deserialize<'de>> Visitor<'de> for TsilCevVisitor<T> {
    type Value = TsilCev<T>;

    fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str("a sequence")
    }

    fn visit_seq<B>(self, mut seq: B) -> Result<Self::Value, B::Error>
    where
        B: SeqAccess<'de>,
    {
        let len = seq.size_hint().unwrap_or(0);

        // let mut tsil_cev = TsilCev::new();
        // use serde::de::Error;
        // tsil_cev.try_reserve(len).map_err(B::Error::custom)?;

        let mut tsil_cev = TsilCev::with_capacity(len);
        unsafe { tsil_cev.cev.set_len(len) };

        // if len is trust len
        for idx in 0..len {
            match seq.next_element()? {
                // safe because len <= seq.len() another break
                Some(x) => unsafe {
                    tsil_cev.cev.get_unchecked_mut(idx).el = x;
                    tsil_cev.cev.set_len(idx + 1);
                },
                _ => break,
            }
        }

        // if len is not trust len
        let mut idx = len;
        while let Some(x) = seq.next_element()? {
            if idx == tsil_cev.capacity() {
                tsil_cev.reserve(1);
            }
            // safe by previous check
            unsafe {
                tsil_cev.cev.get_unchecked_mut(idx).el = x;
                tsil_cev.cev.set_len(idx + 1);
            }
            idx += 1;
        }

        tsil_cev.make_chain_cev();
        Ok(tsil_cev)
    }
}

#[test]
fn serde_1() {
    let mut trust = TsilCev::from(vec![0, 1, 2, 3, 4, 5]);

    let ser = serde_json::to_string(&trust).unwrap();
    let mut des: TsilCev<i32> = serde_json::from_str(&ser).unwrap();

    trust.push_front(-1);
    trust.push_back(10);
    des.push_front(-1);
    des.push_back(10);

    assert_eq!(trust.len(), des.len());
    assert_eq!(trust, des);
    assert_eq!(trust.to_vec(), des.to_vec());
}

#[test]
fn serde_2() {
    let mut trust = TsilCev::from(vec![]);

    let ser = serde_json::to_string(&trust).unwrap();
    let mut des: TsilCev<i32> = serde_json::from_str(&ser).unwrap();

    trust.push_front(-1);
    trust.push_back(10);
    des.push_front(-1);
    des.push_back(10);

    assert_eq!(trust.len(), des.len());
    assert_eq!(trust, des);
    assert_eq!(trust.to_vec(), des.to_vec());
}

#[test]
fn serde_3() {
    let mut trust = TsilCev::from(vec![0, 1, 2, 3, 4, 5]);
    trust.pop_front();
    trust.pop_front();
    trust.pop_back();
    trust.pop_back();

    let ser = serde_json::to_string(&trust).unwrap();
    let mut des: TsilCev<i32> = serde_json::from_str(&ser).unwrap();

    trust.push_front(-1);
    trust.push_back(10);
    des.push_front(-1);
    des.push_back(10);

    assert_eq!(trust.len(), des.len());
    assert_eq!(trust, des);
    assert_eq!(trust.to_vec(), des.to_vec());
}
