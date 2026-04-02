pub(crate) use crate::optim::signature_rewrite::{
    SignatureRewritePlan as PrivateAbiPlan,
    is_owned_private_signature_func as is_owned_private_abi_func,
    propagate_signature_rewrite_types as propagate_private_abi_types,
    retain_higher_order_safe_plans, rewrite_declared_signatures,
};
