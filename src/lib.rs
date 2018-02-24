
extern crate futures;

// BJORN KOLBECK, MIKAEL HOGQVIST, JAN STENDER, FELIX HUPFELD
// Fault-tolerant and Decentralized Lease Coordination in Distributed Systems

// Module rbr defines round-based distributed registers.
pub mod rbr {

	use std::cmp::{Ord};
	use std::marker::{Copy};

    // Register represents a round-based distributed register a defined in the
    // Paxos paper.
	pub struct Register<K, V> {
		read_at: K,
		written_at: K,
		val: Option<V>,
	}

    // ReadValue is the return value of the read operation.
	pub struct ReadValue<K, V> {
		pub written_at: K,
		pub val: Option<V>,
	}

	impl <K: Ord + Copy, V: Copy> Register<K, V> {

		// empty initialize an empty register with k read and write K.
		pub fn empty(k: K) -> Register<K, V> {
			Register{
				read_at: k,
				written_at: k,
				val: None,
			}
		}

		// read reads the register value and returns a non-None optional on
		// success.
        //
        // Lemma R1. Read-abort: If read(k) aborts, then some operation read(k')
        // or write(k', *) was invoked with k' >= k.
		pub fn read(&mut self, k: K) -> Option<ReadValue<K, V>> {
			if self.written_at >= k || self.read_at >= k {
				None
			} else {
				self.read_at = k;
				Some(ReadValue{written_at: self.written_at, val: self.val})
			}
		}

		// write writes val to the register and return if it succeeded.
        //
        // Lemma R2. Write-abort: If write(k,*) aborts,then some operation
        // read(k') or write(k', *) was invoked with k0 > k.
        //
        // Lemma R3. Read-write-commit: If read(k) or write(k,*) commits, then
        // no subsequent read(k') can commit with k' <= k or write(k'',*) can
        // commit with k'' <= k.
		pub fn write(&mut self, k: K, val: V) -> Option<()> {
			if self.written_at > k || self.read_at > k {
				None
			} else {
				self.written_at = k;
				self.val = Some(val);
				Some(())
			}
		}
	}

    pub mod distributed {
        use super::{ReadValue};
        use std::result::{Result};
        use std::io;

        pub enum Failure {
            Abort,
            Error(io::Error),
        }

        pub trait RPC<'a, K, V> {
            fn read(&'a self, K) -> Result<ReadValue<K, V>, Failure>;
            fn write(&'a self, K, V) -> Result<(), Failure>;
        }

        pub trait Node<'a, K, V>: RPC<'a, K, V> {
            fn id(&self) -> u32;
        }

        pub mod threaded {

            use super::{Failure, RPC, Node};
            use rbr::{ReadValue};

            pub struct Cluster<'a, K, V> {
                nodes: [&'a Node<'a, K, V>],
            }

            struct ReadProgress<K, V> {
                quorum: i32, // remaining reads needed to reach quorum
                errors: i32, // remaining errors
                rval: Option<ReadValue<K, V>>, // read value
                failure: Option<Failure>, // last seen error
            }

            impl<K: Ord + Copy, V: Copy> ReadProgress<K, V> {
                fn set(&mut self, result: Result<ReadValue<K, V>, Failure>) {
                    match result {
                        Ok(rval) => {
                            self.quorum -= 1;
                            match self.rval {
                                Some(original_rval) => {
                                    if original_rval.written_at < rval.written_at {
                                        self.rval = Some(rval);
                                    }
                                },
                                None => self.rval = Some(rval),
                            }
                        },
                        Err(failure) => {
                            match failure {
                                Failure::Abort => {
                                    self.errors = 0;
                                    self.failure = Some(Failure::Abort);
                                },
                                Failure::Error(err) => {
                                    self.errors -= 1;
                                    self.failure = Some(Failure::Error(err));
                                }
                            }
                        },
                    }
                }
            }

            struct WriteProgress {
                quorum: i32,
                errors: i32,
                failure: Option<Failure>,
            }

            impl WriteProgress {
                fn set(&mut self, result: Result<(), Failure>) {
                    match result {
                        Ok(rval) => {
                            self.quorum -= 1;
                        },
                        Err(failure) => {
                            match failure {
                                Failure::Abort => {
                                    self.errors = 0;
                                    self.failure = Some(Failure::Abort);
                                },
                                Failure::Error(err) => {
                                    self.errors -= 1;
                                    self.failure = Some(Failure::Error(err));
                                }
                            }
                        },
                    }
                }
            }

            impl<'a, K: Ord + Copy, V: Copy> RPC<
            'a, K, V> for Cluster<'a, K, V> {

                fn read(&self, k: K) -> Result<ReadValue<K, V>, Failure> {

                    let len = self.nodes.len();
                    let quorum =  1 + len / 2;
                    let errors =  len - quorum + 1;

                    let progress = self.nodes.iter()
                        .map(|node| node.read(k))
                        .fold(ReadProgress{ quorum, errors, None, None }, |progress, result| {
                            progress.set(result);
                            progress;
                        })
                        .take_while(|progress, _result| progress.errors > 0 || progress.quorum > 0)
                        .last(|p, _| p);

                    if progress.quorum <= 0 {
                        Ok(progress.rval.unwrap())
                    } else {
                        Err(progress.failure.unwrap())
                    }
                }

                fn write(&self, k: K, v: V) -> Result<(), Failure> {
                }
            }


        }
    }

}

#[cfg(test)]
mod tests {
	use std::time::{Instant, Duration};
	use rbr::{Register};

    #[test]
    fn register_read_write_value() {
    	let now = Instant::now();
        let mut reg : Register<Instant, i32> = Register::empty(now);
        let read = reg.read(now);
 
		assert!(read.is_none(), "read with same k the register was created must fail");

        // This can be suprising at first. But this is straightforward once you
        // consider this is a distributed register. If no other process
        // succesfully read the value then the write can happen.
        assert_eq!(reg.write(now, 1).is_none(), false, "write with the same k must succeed");
        assert_eq!(reg.write(now, 2).is_none(), false, "write with the same k must succeed");
        assert_eq!(reg.write(now, 3).is_none(), false, "write with the same k must succeed");

        let later = now + Duration::from_millis(1);
        let read = reg.read(later);
        assert_eq!(read.is_none(), false, "read must succeed with a later timestamp");
        let rval = read.unwrap();

        assert_eq!(rval.written_at, now);
        assert_eq!(rval.val.unwrap(), 3);

        let read = reg.read(later);
        assert!(read.is_none(), "read with same read k must fail");

        let read = reg.read(now);
        assert!(read.is_none(), "read with an older k must fail");

        assert_eq!(reg.write(now, 10).is_none(), true, "write with a later k must fail");
        assert_eq!(reg.write(later, 1).is_none(), false, "write with a later k must fail");
    }
}
