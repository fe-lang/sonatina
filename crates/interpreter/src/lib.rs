pub mod machine;

#[cfg(test)]
mod tests {
    use machine::Machine;
    use sonatina_ir::{module::FuncRef, Immediate, Module, Type};

    use super::*;

    fn parse_module(input: &str) -> Module {
        match sonatina_parser::parse_module(input) {
            Ok(pm) => pm.module,
            Err(errs) => {
                for err in errs {
                    eprintln!("{}", err.print_to_string("[test]", input, true));
                }
                panic!("parsing failed");
            }
        }
    }

    fn setup(input: &str) -> (Machine, Vec<FuncRef>) {
        let module = parse_module(input);
        let funcs = module.iter_functions().collect();
        (Machine::new(module), funcs)
    }

    #[test]
    fn unary() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i32 {
            block0:
                v1.i32 = not 0.i32;
                v2.i32 = neg v1;
                return v2;
        }
        ";

        let (mut machine, funcs) = setup(input);
        let result = machine.run(funcs[0], vec![]);

        assert_eq!(result.as_imm().unwrap().as_i256().trunc_to_i32(), 1);
    }

    #[test]
    fn binary_arithmetic() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i16 {
            block0:
                v0.i16 = add 3.i16 4.i16;
                v1.i16 = sub v0 1.i16;
                v2.i16 = udiv v1 2.i16;
                v3.i16 =  sdiv v2 65535.i16;
                return v3;
        }
        ";

        let (mut machine, funcs) = setup(input);
        let result = machine.run(funcs[0], vec![]);

        assert_eq!(result.as_imm().unwrap().as_i256().trunc_to_i16(), -3);
    }

    #[test]
    fn cast_sext() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i16 {
            block0:
                v0.i16 = sext -128.i8 i16;
                return v0;
        }
        ";

        let (mut machine, funcs) = setup(input);
        let result = machine.run(funcs[0], vec![]);

        assert_eq!(result.as_imm().unwrap().as_i256().trunc_to_i16(), -128);
    }

    #[test]
    fn cast_zext() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i16 {
            block0:
                v0.i16 = zext -128.i8 i16;
                return v0;
        }
        ";

        let (mut machine, funcs) = setup(input);
        let result = machine.run(funcs[0], vec![]);

        assert_eq!(result.as_imm().unwrap().as_i256().trunc_to_i16(), 128);
    }

    // // TODO: uncomment this when issue https://github.com/fe-lang/sonatina/issues/74 is resolved.
    // // #[test]
    // // fn load_store() {
    // //     let input = "
    // //     target = \"evm-ethereum-london\"

    // //     func private %test() -> i32 {
    // //         block0:
    // //             mstore 0.*i32 1.i32 i32;
    // //             v1.i32 = load 0.*i32 i32;
    // //             return v1;
    // //     }
    // //     ";

    // //     let (mut machine, func) = setup(input);
    // //     let result = machine.run(func, vec![]);

    // //     assert_eq!(result.as_imm().unwrap().as_i256().trunc_to_i32(), 128);
    // // }

    // #[test]
    // fn call() {
    //     let input = "
    //     target = \"evm-ethereum-london\"

    //     func public %test_callee(v0.i8) -> i8 {
    //         block0:
    //             v1.i8 = mul v0 2.i8;
    //             return v1;
    //     }

    //     func public %test() -> i8 {
    //         block0:
    //             v0.i8 = call %test_callee 3.i8;
    //             return v0;
    //     }
    //     ";

    //     let (mut machine, funcs) = setup(input);
    //     let result = machine.run(funcs[1], vec![]);

    //     assert_eq!(result.as_imm().unwrap().as_i256().trunc_to_i8(), 6);
    // }

    // #[test]
    // fn jump() {
    //     let input = "
    //     target = \"evm-ethereum-london\"

    //     func private %test() -> i1 {
    //         block0:
    //             jump block2;
    //         block1:
    //             return 1.i1;
    //         block2:
    //             return 0.i1;
    //     }
    //     ";

    //     let (mut machine, funcs) = setup(input);
    //     let result = machine.run(funcs[0], vec![]);

    //     assert!(!result.as_imm().unwrap().as_i256().trunc_to_i1());
    // }

    // #[test]
    // fn branch() {
    //     let input = "
    //     target = \"evm-ethereum-london\"

    //     func private %test() -> i8 {
    //         block0:
    //             br 1.i1 block1 block2;
    //         block1:
    //             return 1.i8;
    //         block2:
    //             return 2.i8;
    //     }
    //     ";

    //     let (mut machine, funcs) = setup(input);
    //     let result = machine.run(funcs[0], vec![]);

    //     assert_eq!(result.as_imm().unwrap().as_i256().trunc_to_i8(), 1);
    // }

    // #[test]
    // fn br_table() {
    //     let input = "
    //     target = \"evm-ethereum-london\"

    //     func private %test() -> i64 {
    //         block0:
    //             br_table 1.i64 (0.i64 block1) (1.i64 block2);
    //         block1:
    //             return 1.i64;
    //         block2:
    //             return 2.i64;
    //         block3:
    //             return 3.i64;
    //     }
    //     ";

    //     let (mut machine, funcs) = setup(input);
    //     let result = machine.run(funcs[0], vec![]);

    //     assert_eq!(result.as_imm().unwrap().as_i256().trunc_to_i64(), 2);
    // }

    #[test]
    fn phi() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i8 {
            block0:
                br 1.i1 block1 block2;
            block1:
                jump block2;
            block2:
                v0.i8 = phi (1.i8 block0) (-1.i8 block1);
                return v0;
        }
        ";

        let (mut machine, funcs) = setup(input);
        let result = machine.run(funcs[0], vec![]);

        assert_eq!(result.as_imm().unwrap().as_i256().trunc_to_i8(), -1);
    }

    #[test]
    fn gep() {
        let input = "
        target = \"evm-ethereum-london\"

        type @s1 = {i32, i64, i1};

        func private %test(v0.i256) -> *i1 {
            block0:
                v1.*@s1 = int_to_ptr v0 *@s1;
                v2.*i1 = gep v1 0.i256 2.i256;
                return v2;
        }
        ";

        let (mut machine, funcs) = setup(input);
        let arg = Immediate::zero(Type::I256);
        let result = machine.run(funcs[0], vec![arg.into()]);

        assert_eq!(result.as_imm().unwrap().as_i256().trunc_to_i64(), 12);
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn gep_ptr_ty() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test(v0.i256) -> **i32 {
            block0:
                v1.*[*i32; 3] = int_to_ptr v0 *[*i32; 3];
                v2.**i32 = gep v1 0.i256 2.i256;
                return v2;
        }
        ";

        let (mut machine, funcs) = setup(input);
        let arg = Immediate::zero(Type::I256);
        let result = machine.run(funcs[0], vec![arg.into()]);

        assert_eq!(result.as_imm().unwrap().as_i256().trunc_to_i64(), 64);
    }

    #[test]
    fn gep_nested_aggr_ty() {
        let input = "
        target = \"evm-ethereum-london\"

        type @s1 = {i32, [i16; 3], [i8; 2]};

        func private %test(v0.i256) -> *i8 {
            block0:
                v1.*@s1 = int_to_ptr v0 *@s1;
                v2.*i8 = gep v1 0.i256 2.i256 1.i256;
                return v2;
        }
        ";

        let (mut machine, funcs) = setup(input);
        let arg = Immediate::zero(Type::I256);
        let result = machine.run(funcs[0], vec![arg.into()]);

        assert_eq!(result.as_imm().unwrap().as_i256().trunc_to_i64(), 11);
    }
}
