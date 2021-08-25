use ::ghost_cell::*;

struct Database {}

struct Iterator<'a> {
    _db: &'a Database,
}

impl Database {
    fn iterator<'a>(&'a self) -> Iterator<'a> {
        Iterator { _db: self }
    }
}

struct DbIter<'a, 'id> {
    _db: &'a GhostCell<'id, Database>,
    _iter: &'a GhostCell<'id, Iterator<'a>>,
}

fn my_function<'a, 'id>(_dbi: DbIter<'a, 'id>) {}

fn main() {
    GhostToken::new(|token| {
        let db = Database {};
        let gdb = GhostCell::new(db);
        let iter = gdb.borrow(&token).iterator();
        let giter = GhostCell::new(iter);
        let db_iter = DbIter {
            _db: &gdb,
            _iter: &giter,
        };
        my_function(db_iter)
    })
}
