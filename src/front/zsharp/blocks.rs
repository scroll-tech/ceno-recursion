use zokrates_pest_ast as ast;
use crate::front::zsharp::ZGen;
use crate::front::zsharp::debug;
use crate::front::zsharp::PathBuf;

pub struct B<'ast> {
    blocks: Vec<Vec<&'ast ast::Statement<'ast>>>,
    bl_len: usize
}

impl<'ast> B<'ast> {
    fn new() -> Self {
        let mut input = Self {
            blocks: Vec::new(),
            bl_len: 1
        };
        input.blocks.push(Vec::new());
        input
    }

    pub fn pretty(&self) {
        for i in 0..self.bl_len {
            println!("\nBlock {}:", i);
            for j in &self.blocks[i] {
                println!("{}", j.span().as_str());
            }
        }
    }
}

impl<'ast> ZGen<'ast> {
    pub fn bl_const_entry_fn(&'ast self, n: &str) -> B<'ast> {
        debug!("Const entry: {}", n);
        let (f_file, f_name) = self.deref_import(n);
        if let Some(f) = self.functions.get(&f_file).and_then(|m| m.get(&f_name)) {
            if !f.generics.is_empty() {
                panic!("const_entry_fn cannot be called on a generic function")
            } else if !f.parameters.is_empty() {
                panic!("const_entry_fn must be called on a function with zero arguments")
            }
        } else {
            panic!(
                "No function '{:?}//{}' attempting const_entry_fn",
                &f_file, &f_name
            );
        }

        self.bl_function_call_impl_::<true>(f_file, f_name)
            .unwrap_or_else(|e| panic!("const_entry_fn failed: {}", e))
    }

    fn bl_function_call_impl_<const IS_CNST: bool>(
        &self,
        f_path: PathBuf,
        f_name: String,
    ) -> Result<B, String> {
        if IS_CNST {
            debug!("Const function call: {} {:?}", f_name, f_path);
        } else {
            debug!("Function call: {} {:?}", f_name, f_path);
        }
        let f = self
            .functions
            .get(&f_path)
            .ok_or_else(|| format!("No file '{:?}' attempting fn call", &f_path))?
            .get(&f_name)
            .ok_or_else(|| format!("No function '{}' attempting fn call", &f_name))?;

        let mut blks = B::new();
        for s in &f.statements {
            blks = self.bl_stmt_impl_::<IS_CNST>(blks, s)?;
        }

        Ok(blks)
    }

    fn bl_stmt_impl_<const IS_CNST: bool>(&'ast self, mut blks: B<'ast>, s: &'ast ast::Statement<'ast>) -> Result<B, String> {
        if IS_CNST {
            debug!("Const stmt: {}", s.span().as_str());
        } else {
            debug!("Stmt: {}", s.span().as_str());
        }

        match s {
            ast::Statement::Return(_) => {
                blks.blocks[blks.bl_len - 1].push(s);
                Ok(blks)
            }
            ast::Statement::Assertion(_) => {
                blks.blocks[blks.bl_len - 1].push(s);
                Ok(blks)
            }
            ast::Statement::Iteration(it) => {
                blks.blocks[blks.bl_len - 1].push(s);
                blks.blocks.push(Vec::new());
                blks.bl_len += 1;
                for body in &it.statements {
                    blks = self.bl_stmt_impl_::<IS_CNST>(blks, body)?;
                }
                blks.blocks.push(Vec::new());
                blks.bl_len += 1;
                Ok(blks)
            }
            ast::Statement::Definition(_) => {
                blks.blocks[blks.bl_len - 1].push(s);
                Ok(blks)
            }
        }
    }
}
