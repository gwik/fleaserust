extern crate futures;

// BJORN KOLBECK, MIKAEL HOGQVIST, JAN STENDER, FELIX HUPFELD
// Fault-tolerant and Decentralized Lease Coordination in Distributed Systems

// Module rbr defines round-based distributed registers.
pub mod rbr {

	use std::cmp::{Ord};
	use std::marker::{Copy};

    // Register represents a round-based distributed register a defined in the
    // Paxos paper.
    #[derive(Debug)]
	pub struct Register<K, V> {
		read_at: K,
		written_at: K,
		val: Option<V>,
	}

    // ReadValue is the return value of the read operation.
    #[derive(Debug, Copy, Clone)]
	pub struct ReadValue<K, V> {
		pub written_at: K,
		pub val: Option<V>,
	}

	impl <'a, K: Ord + Copy, V: Clone> Register<K, V> {

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
				Some(ReadValue{written_at: self.written_at, val: self.val.clone()})
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
		pub fn write(&mut self, k: K, v: V) -> Option<()> {
			if self.written_at > k || self.read_at > k {
				None
			} else {
				self.written_at = k;
				self.val = Some(v);
				Some(())
			}
		}
	}

    pub mod distributed {
        use super::{ReadValue};
        use std::vec::{Vec};
        use std::result::{Result};
        use std::io;

        pub enum Failure {
            Abort,
            Error(io::Error),
        }

        pub trait RPC<'a, K: 'a, V: 'a> {
            fn read(&'a self, K) -> Result<ReadValue<K, V>, Failure>;
            // fn write(&self, K, &V) -> Result<(), Failure>;
        }

        pub trait Node<'a, K: 'a, V: 'a>: RPC<'a, K, V> {
            fn id(&self) -> u32;
        }
 
        pub struct Cluster<'a, K: 'a, V: 'a> {
            nodes: Vec<&'a Node<'a, K, V>>,
        }

        impl<'a, K: Ord + Copy, V: Clone> Cluster<'a, K, V> {
            pub fn new(nodes: Vec<&'a Node<'a, K, V>>) -> Cluster<K, V> {
                Cluster{nodes: nodes}
            }
        }

        impl<'a, 'b, K: Ord + Copy + 'a, V: Clone + 'a> RPC<'a, K, V> for Cluster<'b, K, V> {

            fn read(&self, k: K) -> Result<ReadValue<K, V>, Failure> {

                let len: i32 = self.nodes.len() as i32;
                let mut quorum =  1 + len / 2;
                let mut errors =  len - quorum + 1;
                let mut rval : Option<ReadValue<K, V>> = None;
                let mut error : Failure = Failure::Abort;

                for node in self.nodes.iter() {
                    let nval : Result<Option<ReadValue<K, V>>, Failure> = {
                        match node.read(k) {
                            Ok(node_rval) => {
                                match rval {
                                    Some(ref rv) => {
                                        if rv.written_at < node_rval.written_at {
                                           Ok(Some(node_rval))
                                        } else {
                                           Ok(None)
                                        }
                                    },
                                    None => {
                                        Ok(Some(node_rval))
                                    }
                                }
                            },
                            Err(e) => Err(e),
                        }
                    };

                    match nval {
                        Ok(ov) => {
                            quorum -= 1;
                            match ov {
                                Some(rv) => {
                                    rval = Some(rv)
                                },
                                None => {},
                            }
                        },
                        Err(Failure::Abort) => return Err(Failure::Abort),
                        Err(e) => {
                            errors -= 1;
                            error = e;
                        },
                    }

                    if errors <= 0 || quorum <= 0 {
                        break
                    }
                }

                if quorum <= 0 {
                    match rval {
                        Some(v) => return Ok(v),
                        None => return Err(error),
                    }
                }
                return Err(error)
            }
        }
    }

}

#[cfg(test)]
mod tests {
    use std::time::{Instant, Duration};
    use std::result::{Result};
    use std::cell::{RefCell};
    use std::sync::{Mutex};

    use rbr::*;
    use rbr::distributed::*;

    #[test]
    fn register_read_write_value() {
    	let now = Instant::now();
        let mut reg : Register<Instant, i32> = Register::empty(now);

        assert!(reg.read(now).is_none(), "read with same k the register was created must fail");

        // This can be suprising at first. But this is straightforward once you
        // consider this is a distributed register. If no other process
        // succesfully read the value then the write can happen.
        assert_eq!(reg.write(now, 1).is_none(), false, "write with the same k must succeed");
        assert_eq!(reg.write(now, 2).is_none(), false, "write with the same k must succeed");
        assert_eq!(reg.write(now, 3).is_none(), false, "write with the same k must succeed");

        let later = now + Duration::from_millis(1);
        {
            let read = reg.read(later);
            assert_eq!(read.is_none(), false, "read must succeed with a later timestamp");
            let rval = read.unwrap();

            assert_eq!(rval.written_at, now);
            assert_eq!(rval.val.unwrap(), 3);
        }

        assert!(reg.read(later).is_none(), "read with same read k must fail");
        assert!(reg.read(now).is_none(), "read with an older k must fail");

        assert_eq!(reg.write(now, 10).is_none(), true, "write with a later k must fail");
        assert_eq!(reg.write(later, 1).is_none(), false, "write with a later k must fail");
    }

    struct TestOKNode<'a, K: 'a, V: 'a> {
        id:  u32,
        reg: Mutex<&'a RefCell<Register<K, V>>>,
    }

    impl<'a, K: Ord + Copy + 'a, V: Clone + 'a> TestOKNode<'a, K, V> {
        fn new(id: u32, reg: &'a RefCell<Register<K,V>>) -> TestOKNode<'a, K, V> {
            TestOKNode{id: id, reg: Mutex::new(reg)}
        }
    }

    impl<'a, K: Ord + Copy + 'a, V: Clone + 'a> Node<'a, K, V> for TestOKNode<'a, K, V> {
        fn id(&self) -> u32 {
            self.id
        }
    }

    impl<'a, K: Ord + Copy + 'a, V: Clone + 'a> RPC<'a, K, V> for TestOKNode<'a, K, V> {
        fn read(&'a self, k: K) -> Result<ReadValue<K, V>, Failure> {
            match self.reg.lock().unwrap().borrow_mut().read(k) {
                Some(rval) => Ok(rval),
                None => Err(Failure::Abort),
            }
        }
    }

    #[test]
    fn cluster_read() {
        let k = 0i32;

        let regs : Vec<RefCell<Register<i32, i64>>> = vec![
            { let k = k; RefCell::new(Register::empty(k)) },
            { let k = k; RefCell::new(Register::empty(k)) },
        ];

        let nodes : Vec<TestOKNode<i32, i64>> = vec![
            { TestOKNode::new(0, &regs[0]) },
            { TestOKNode::new(1, &regs[1]) },
        ];

        let nodes : Vec<&Node<i32, i64>> = vec![
            &nodes[0],
            &nodes[1],
        ];

        let cluster = Cluster::new(nodes);
        {
            let k = 1i32;
            assert_eq!(cluster.read(k).is_ok(), true);
        }
        {
            let k = 1i32;
            assert_eq!(cluster.read(k).is_err(), true);
        }
        {
            let k = 2i32;
            assert_eq!(cluster.read(k).is_ok(), true);
        }
        {
            let k = 3i32;
            regs[0].borrow_mut().read(k);

            let res = cluster.read(k);
            assert_eq!(res.is_err(), true);
        }

    }

}
