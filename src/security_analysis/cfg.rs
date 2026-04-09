use move_compiler::{
    cfgir::{ast as G, cfg::ImmForwardCFG},
    hlir::ast as H,
    parser::ast::FunctionName,
};

pub fn function_cfg(
    function: &G::Function,
) -> Option<(
    H::Label,
    G::BasicBlocks,
    std::collections::BTreeMap<H::Label, G::BlockInfo>,
)> {
    match &function.body.value {
        G::FunctionBody_::Defined {
            start,
            block_info,
            blocks,
            ..
        } => Some((*start, blocks.clone(), block_info.clone())),
        G::FunctionBody_::Native => None,
    }
}

pub fn build_cfg<'a>(
    function: &'a G::Function,
) -> Option<(
    ImmForwardCFG<'a>,
    &'a G::BasicBlocks,
    &'a std::collections::BTreeMap<H::Label, G::BlockInfo>,
)> {
    match &function.body.value {
        G::FunctionBody_::Defined {
            start,
            block_info,
            blocks,
            ..
        } => {
            let (cfg, _) = ImmForwardCFG::new(*start, blocks, block_info.iter());
            Some((cfg, blocks, block_info))
        }
        G::FunctionBody_::Native => None,
    }
}

pub fn function_name_text(name: &FunctionName) -> String {
    name.to_string()
}
