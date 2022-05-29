use ic_crypto_sha256::Sha256;
use std::cell::{BorrowMutError, RefCell};
use std::error::Error;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Debug)]
pub struct MaybeFileBacked {
    path: Option<PathBuf>,
    bytes: RefCell<Option<Vec<u8>>>,
}

impl MaybeFileBacked {
    pub fn new_from_path<P: AsRef<Path>>(path: P) -> Self {
        MaybeFileBacked {
            path: Some(path.as_ref().to_path_buf()),
            bytes: RefCell::new(None),
        }
    }

    pub fn new_from_bytes<P: AsRef<Path>>(bytes: Vec<u8>) -> Self {
        MaybeFileBacked {
            path: None,
            bytes: RefCell::new(Some(bytes)),
        }
    }

    pub fn new_with_bytes_at_path<
        P: AsRef<Path>,
        E: Error + From<BorrowMutError> + From<std::io::Error>,
    >(
        path: P,
        content: Vec<u8>,
    ) -> Result<Self, E> {
        let backed = MaybeFileBacked {
            path: Some(path.as_ref().to_path_buf()),
            bytes: RefCell::new(None),
        };
        backed.replace_bytes::<E>(content)?;
        Ok(backed)
    }

    pub fn flush(&self) {}

    pub fn replace_bytes<E: Error + From<BorrowMutError> + From<std::io::Error>>(
        &mut self,
        content: Vec<u8>,
    ) -> Result<(), E> {
        let mut b = self.bytes.try_borrow_mut()?;
        match &self.path {
            Some(p) => {
                fs::write(p, &content)?;
                *b = Some(content);
                Ok(())
            }
            None => Ok(()),
        }
    }

    pub fn get_path(&self) -> Option<PathBuf> {
        self.path
    }

    pub fn with_bytes<'a, R, E: Error + From<BorrowMutError> + From<std::io::Error>>(
        &self,
        f: impl FnOnce(&[u8]) -> Result<R, E> + 'a,
    ) -> Result<R, E> {
        let mut b = self.bytes.try_borrow_mut()?;
        match &*b {
            Some(bytes) => (f)(&bytes),
            None => match &self.path {
                Some(p) => {
                    let content = fs::read(p)?;
                    let res = (f)(&content);
                    *b = Some(content);
                    res
                }
                None => (f)(&[]),
            },
        }
    }

    pub fn compute_hash<E: Error + From<BorrowMutError> + From<std::io::Error>>(
        &self,
    ) -> Result<[u8; 32], E> {
        self.with_bytes(|b| Ok(Sha256::hash(b)))
    }
}
