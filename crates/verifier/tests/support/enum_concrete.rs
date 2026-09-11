//! Bounded concrete executions for the enum contract, independent of verifier facts.
//!
//! Each allocation execution gets a new object. Values contain actual references
//! and copies of nested storage. No join, provenance analysis or proof transfer is
//! imported from the verifier. Unsupported instructions and exploration exhaustion
//! are explicit failures of the test oracle, never successful verification.
use std::collections::{BTreeMap, BTreeSet};

use sonatina_ir::{
    BlockId, Function, InstId, Type, Value, ValueId,
    inst::{arith, cmp, control_flow, data, downcast},
    module::ModuleCtx,
    types::CompoundType,
};
use sonatina_parser::parse_module;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Step {
    Field(usize),
    Payload(usize, usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Location {
    object: usize,
    path: Vec<Step>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct View {
    location: Location,
    guards: Vec<(Location, usize)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Data {
    Scalar(u64),
    Reference(Option<View>),
    RawPointer(Option<usize>),
    Product(Vec<Node>),
    Enum {
        tag: usize,
        payloads: Vec<Vec<Node>>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Node {
    // For an enum this is tag initialization; products use their children.
    initialized: bool,
    data: Data,
}

impl Node {
    fn scalar(value: u64) -> Self {
        Self {
            initialized: true,
            data: Data::Scalar(value),
        }
    }

    fn reference(view: View) -> Self {
        Self {
            initialized: true,
            data: Data::Reference(Some(view)),
        }
    }

    fn uninitialized(ctx: &ModuleCtx, ty: Type) -> Self {
        let data = match ty {
            Type::Compound(id) => ctx.with_ty_store(|types| match types.resolve_compound(id) {
                CompoundType::Struct(record) => Data::Product(
                    record
                        .fields
                        .iter()
                        .map(|&ty| Self::uninitialized(ctx, ty))
                        .collect(),
                ),
                CompoundType::Array { elem, len } => {
                    assert!(*len <= 16, "concrete oracle array bound exceeded");
                    Data::Product(vec![Self::uninitialized(ctx, *elem); *len])
                }
                CompoundType::Enum(enumeration) => Data::Enum {
                    tag: 0,
                    payloads: enumeration
                        .variants
                        .iter()
                        .map(|variant| {
                            variant
                                .fields
                                .iter()
                                .map(|&ty| Self::uninitialized(ctx, ty))
                                .collect()
                        })
                        .collect(),
                },
                CompoundType::ObjRef(_) => Data::Reference(None),
                CompoundType::Ptr(_) => Data::RawPointer(None),
                other => panic!("unsupported concrete type {other:?}"),
            }),
            _ => Data::Scalar(0),
        };
        Self {
            initialized: false,
            data,
        }
    }

    fn initialized_values(&self) -> Vec<Self> {
        let data = match &self.data {
            Data::Product(fields) => Self::products(fields)
                .into_iter()
                .map(Data::Product)
                .collect(),
            Data::Enum { payloads, .. } => payloads
                .iter()
                .enumerate()
                .flat_map(|(tag, fields)| {
                    Self::products(fields).into_iter().map(move |fields| {
                        let mut payloads = payloads.clone();
                        payloads[tag] = fields;
                        Data::Enum { tag, payloads }
                    })
                })
                .collect(),
            Data::Scalar(_) => vec![Data::Scalar(17)],
            Data::RawPointer(_) => vec![Data::RawPointer(None)],
            Data::Reference(_) => panic!("supply concrete reference inputs explicitly"),
        };
        data.into_iter()
            .map(|data| Self {
                initialized: true,
                data,
            })
            .collect()
    }

    fn products(fields: &[Self]) -> Vec<Vec<Self>> {
        fields.iter().fold(vec![vec![]], |prefixes, field| {
            prefixes
                .into_iter()
                .flat_map(|prefix| {
                    field.initialized_values().into_iter().map(move |value| {
                        let mut values = prefix.clone();
                        values.push(value);
                        values
                    })
                })
                .collect()
        })
    }

    fn readable(&self) -> bool {
        match &self.data {
            Data::Product(fields) => fields.iter().all(Self::readable),
            Data::Enum { tag, payloads } => {
                self.initialized && payloads[*tag].iter().all(Self::readable)
            }
            _ => self.initialized,
        }
    }

    fn clear_readability(&mut self) {
        self.initialized = false;
        match &mut self.data {
            Data::Product(fields) => fields.iter_mut().for_each(Self::clear_readability),
            Data::Enum { payloads, .. } => payloads
                .iter_mut()
                .flatten()
                .for_each(Self::clear_readability),
            _ => {}
        }
        // Retain reference bytes even when their logical payload is inactive.
    }

    fn child(&self, step: &Step) -> &Self {
        match (&self.data, step) {
            (Data::Product(fields), Step::Field(index)) => &fields[*index],
            (Data::Enum { payloads, .. }, Step::Payload(tag, index)) => &payloads[*tag][*index],
            _ => panic!("ill-shaped concrete projection"),
        }
    }

    fn child_mut(&mut self, step: &Step) -> &mut Self {
        match (&mut self.data, step) {
            (Data::Product(fields), Step::Field(index)) => &mut fields[*index],
            (Data::Enum { payloads, .. }, Step::Payload(tag, index)) => &mut payloads[*tag][*index],
            _ => panic!("ill-shaped concrete projection"),
        }
    }

    fn references(&self, objects: &mut Vec<usize>) {
        match &self.data {
            Data::Reference(Some(view)) => objects.push(view.location.object),
            Data::Product(fields) => fields.iter().for_each(|field| field.references(objects)),
            Data::Enum { payloads, .. } => payloads
                .iter()
                .flatten()
                .for_each(|field| field.references(objects)),
            _ => {}
        }
    }

    fn view(&self) -> View {
        let Data::Reference(Some(view)) = &self.data else {
            panic!("concrete reference required");
        };
        assert!(self.initialized, "uninitialized concrete reference operand");
        view.clone()
    }

    fn integer(&self) -> u64 {
        assert!(self.initialized, "undefined concrete integer operand");
        match self.data {
            Data::Scalar(value) => value,
            _ => panic!("concrete scalar required"),
        }
    }
}

#[derive(Clone, Debug)]
struct Object {
    value: Node,
    raw_bytes: Option<usize>,
}

#[derive(Clone, Debug, Default)]
struct World {
    values: BTreeMap<ValueId, Node>,
    objects: Vec<Object>,
    exposed: BTreeSet<usize>,
}

impl World {
    fn allocate(&mut self, value: Node, raw_bytes: Option<usize>) -> View {
        let object = self.objects.len();
        self.objects.push(Object { value, raw_bytes });
        View {
            location: Location {
                object,
                path: vec![],
            },
            guards: vec![],
        }
    }

    fn value(&self, func: &Function, value: ValueId) -> Node {
        match func.dfg.value(value) {
            Value::Immediate { imm, .. } => {
                Node::scalar(imm.to_nonnegative_usize().expect("small model integer") as u64)
            }
            Value::Undef { ty } => Node::uninitialized(func.ctx(), *ty),
            _ => self.values[&value].clone(),
        }
    }

    fn at(&self, location: &Location) -> &Node {
        location
            .path
            .iter()
            .fold(&self.objects[location.object].value, Node::child)
    }

    fn at_mut(&mut self, location: &Location) -> &mut Node {
        location
            .path
            .iter()
            .fold(&mut self.objects[location.object].value, Node::child_mut)
    }

    fn guards_hold(&self, view: &View) -> bool {
        view.guards.iter().all(|(location, variant)| {
            let node = self.at(location);
            matches!(node.data, Data::Enum { tag, .. } if node.initialized && tag == *variant)
        })
    }

    fn close_exposure(&mut self) {
        let mut pending: Vec<_> = self.exposed.iter().copied().collect();
        let mut seen = BTreeSet::new();
        while let Some(object) = pending.pop() {
            if seen.insert(object) {
                self.exposed.insert(object);
                self.objects[object].value.references(&mut pending);
            }
        }
    }
}

#[derive(Debug, Default)]
pub struct Execution {
    pub reads: BTreeMap<InstId, bool>,
    pub returned: usize,
    pub assumptions_pruned: usize,
    pub exhausted: usize,
    pub max_objects: usize,
}

impl Execution {
    fn read(&mut self, inst: InstId, valid: bool) {
        *self.reads.entry(inst).or_insert(true) &= valid;
    }

    pub fn invalid_reads(&self) -> usize {
        self.reads.values().filter(|&&valid| !valid).count()
    }
}

pub fn execute(source: &str, instruction_limit: usize) -> Execution {
    let parsed = parse_module(source).expect("contract fixture parses");
    let func = parsed
        .module
        .funcs()
        .into_iter()
        .find(|&func| {
            parsed
                .module
                .ctx
                .func_sig(func, |sig| sig.name() == "entry")
        })
        .expect("entry function");
    parsed.module.func_store.view(func, |func| {
        let mut worlds = vec![World::default()];
        for &arg in &func.arg_values {
            let ty = func.dfg.value_ty(arg);
            worlds = worlds
                .into_iter()
                .flat_map(|world| {
                    if let Some(CompoundType::ObjRef(elem)) = ty.resolve_compound(func.ctx()) {
                        Node::uninitialized(func.ctx(), elem)
                            .initialized_values()
                            .into_iter()
                            .map(|node| {
                                let mut world = world.clone();
                                let view = world.allocate(node, None);
                                world.exposed.insert(view.location.object);
                                world.values.insert(arg, Node::reference(view));
                                world
                            })
                            .collect::<Vec<_>>()
                    } else {
                        let values = if ty == Type::I1 {
                            vec![Node::scalar(0), Node::scalar(1)]
                        } else {
                            Node::uninitialized(func.ctx(), ty).initialized_values()
                        };
                        values
                            .into_iter()
                            .map(|value| {
                                let mut world = world.clone();
                                world.values.insert(arg, value);
                                world
                            })
                            .collect()
                    }
                })
                .collect();
            assert!(worlds.len() <= 4096, "concrete input bound exceeded");
        }
        let entry = func.layout.entry_block().expect("entry block");
        let mut pending: Vec<_> = worlds
            .into_iter()
            .map(|world| (entry, None, world, 0, 0))
            .collect();
        let mut execution = Execution::default();
        while let Some(work) = pending.pop() {
            execute_block(func, work, instruction_limit, &mut pending, &mut execution);
            assert!(pending.len() <= 4096, "concrete path bound exceeded");
        }
        execution
    })
}

// A work item keeps the actual predecessor and its values; phi assignments are
// simultaneous. This also preserves older dynamic references across backedges.
type Work = (BlockId, Option<BlockId>, World, usize, usize);

fn execute_block(
    func: &Function,
    (block, pred, mut world, mut steps, offset): Work,
    limit: usize,
    pending: &mut Vec<Work>,
    execution: &mut Execution,
) {
    let incoming = world.values.clone();
    for (index, inst) in func.layout.iter_inst(block).enumerate().skip(offset) {
        steps += 1;
        if steps > limit {
            execution.exhausted += 1;
            return;
        }
        let data = func.dfg.inst(inst);
        let is = func.inst_set();
        let value = |id| world.value(func, id);
        let output = if let Some(phi) = downcast::<&control_flow::Phi>(is, data) {
            let arg = phi
                .args()
                .iter()
                .find(|(_, block)| Some(*block) == pred)
                .expect("phi incoming predecessor")
                .0;
            Some(incoming.get(&arg).cloned().unwrap_or_else(|| value(arg)))
        } else if let Some(alloc) = downcast::<&data::ObjAlloc>(is, data) {
            let view = world.allocate(Node::uninitialized(func.ctx(), *alloc.ty()), None);
            Some(Node::reference(view))
        } else if let Some(alloc) = downcast::<&data::Alloca>(is, data) {
            let view = world.allocate(
                Node::uninitialized(func.ctx(), *alloc.ty()),
                Some(
                    func.ctx()
                        .size_of(*alloc.ty())
                        .expect("raw allocation size"),
                ),
            );
            Some(Node {
                initialized: true,
                data: Data::RawPointer(Some(view.location.object)),
            })
        } else if let Some(proj) = downcast::<&data::EnumProj>(is, data) {
            let mut view = value(*proj.object()).view();
            let variant = proj.variant().index() as usize;
            let index = value(*proj.field()).integer() as usize;
            view.guards.push((view.location.clone(), variant));
            view.location.path.push(Step::Payload(variant, index));
            Some(Node::reference(view))
        } else if let Some(proj) = downcast::<&data::ObjProj>(is, data) {
            let mut args = proj.values().iter();
            let mut view = value(*args.next().expect("projection base")).view();
            view.location
                .path
                .extend(args.map(|&index| Step::Field(value(index).integer() as usize)));
            Some(Node::reference(view))
        } else if let Some(index) = downcast::<&data::ObjIndex>(is, data) {
            let mut view = value(*index.object()).view();
            view.location
                .path
                .push(Step::Field(value(*index.index()).integer() as usize));
            Some(Node::reference(view))
        } else if let Some(assertion) = downcast::<&data::EnumAssertVariantRef>(is, data) {
            let reference = value(*assertion.object());
            let view = reference.view();
            let node = world.at(&view.location);
            if !matches!(node.data, Data::Enum { tag, .. } if tag == assertion.variant().index() as usize)
                || !node.readable()
            {
                execution.assumptions_pruned += 1;
                return;
            }
            Some(reference)
        } else if let Some(load) = downcast::<&data::ObjLoad>(is, data) {
            let view = value(*load.object()).view();
            let node = world.at(&view.location);
            if !view.guards.is_empty() {
                execution.read(inst, world.guards_hold(&view) && node.readable());
            }
            Some(node.clone())
        } else if let Some(tag) = downcast::<&data::EnumGetTag>(is, data) {
            let view = value(*tag.object()).view();
            let node = world.at(&view.location);
            if !view.guards.is_empty() {
                execution.read(inst, world.guards_hold(&view) && node.initialized);
            }
            let Data::Enum { tag, .. } = node.data else {
                panic!("tag of non-enum");
            };
            Some(Node::scalar(tag as u64))
        } else if let Some(store) = downcast::<&data::ObjStore>(is, data) {
            let view = value(*store.object()).view();
            let stored = value(*store.value());
            *world.at_mut(&view.location) = stored;
            world.close_exposure();
            None
        } else if let Some(write) = downcast::<&data::EnumSetTag>(is, data) {
            let view = value(*write.object()).view();
            let node = world.at_mut(&view.location);
            let Data::Enum { tag, payloads } = &mut node.data else {
                panic!("tag write to non-enum");
            };
            let selected = write.variant().index() as usize;
            if !node.initialized || *tag != selected {
                payloads[selected]
                    .iter_mut()
                    .for_each(Node::clear_readability);
            }
            *tag = selected;
            node.initialized = true;
            None
        } else if let Some(write) = downcast::<&data::EnumWriteVariant>(is, data) {
            let view = value(*write.object()).view();
            let fields = write.values().iter().map(|&arg| value(arg)).collect();
            let node = world.at_mut(&view.location);
            let Data::Enum { tag, payloads } = &mut node.data else {
                panic!("variant write to non-enum");
            };
            *tag = write.variant().index() as usize;
            payloads[*tag] = fields;
            node.initialized = true;
            world.close_exposure();
            None
        } else if let Some(insert) = downcast::<&data::InsertValue>(is, data) {
            let mut dest = value(*insert.dest());
            *dest.child_mut(&Step::Field(value(*insert.idx()).integer() as usize)) =
                value(*insert.value());
            Some(dest)
        } else if let Some(extract) = downcast::<&data::ExtractValue>(is, data) {
            Some(
                value(*extract.dest())
                    .child(&Step::Field(value(*extract.idx()).integer() as usize))
                    .clone(),
            )
        } else if let Some(make) = downcast::<&data::EnumMake>(is, data) {
            let mut node = Node::uninitialized(func.ctx(), *make.ty());
            let Data::Enum { tag, payloads } = &mut node.data else {
                panic!("make of non-enum");
            };
            *tag = make.variant().index() as usize;
            payloads[*tag] = make.values().iter().map(|&arg| value(arg)).collect();
            node.initialized = true;
            Some(node)
        } else if let Some(tag) = downcast::<&data::EnumTag>(is, data) {
            let Data::Enum { tag, .. } = value(*tag.value()).data else {
                panic!("tag of non-enum")
            };
            Some(Node::scalar(tag as u64))
        } else if let Some(test) = downcast::<&data::EnumIsVariant>(is, data) {
            let Data::Enum { tag, .. } = value(*test.value()).data else {
                panic!("test of non-enum")
            };
            Some(Node::scalar(u64::from(
                tag == test.variant().index() as usize,
            )))
        } else if let Some(assertion) = downcast::<&data::EnumAssertVariant>(is, data) {
            let node = value(*assertion.value());
            if !matches!(node.data, Data::Enum { tag, .. } if tag == assertion.variant().index() as usize)
                || !node.readable()
            {
                execution.assumptions_pruned += 1;
                return;
            }
            None
        } else if let Some(extract) = downcast::<&data::EnumExtract>(is, data) {
            let node = value(*extract.value());
            let variant = extract.variant().index() as usize;
            let field = node.child(&Step::Payload(
                variant,
                value(*extract.field()).integer() as usize,
            ));
            execution.read(
                inst,
                matches!(node.data, Data::Enum { tag, .. } if node.initialized && tag == variant)
                    && field.readable(),
            );
            Some(field.clone())
        } else if let Some(materialize) = downcast::<&data::ObjMaterializeStack>(is, data) {
            let object = value(*materialize.object()).view().location.object;
            world.exposed.insert(object);
            world.close_exposure();
            Some(Node {
                initialized: true,
                data: Data::RawPointer(Some(object)),
            })
        } else if let Some(store) = downcast::<&data::Mstore>(is, data) {
            let Data::RawPointer(target) = value(*store.addr()).data else {
                panic!("raw pointer required");
            };
            let affected: Vec<_> = target.map_or_else(
                || world.exposed.iter().copied().collect(),
                |target| vec![target],
            );
            // Opaque raw interference is nondeterministic at the model boundary.
            // Explore missing all objects and invalidating each reachable object.
            // The bounded separate-allocation fixtures use in-bounds scalar writes.
            for object in affected {
                if let Some(bytes) = world.objects[object].raw_bytes {
                    assert!(
                        func.ctx().size_of(*store.ty()).expect("raw write size") <= bytes,
                        "out-of-bounds raw writes are outside this concrete oracle"
                    );
                } else {
                    let mut changed = world.clone();
                    changed.objects[object].value.clear_readability();
                    pending.push((block, pred, changed, steps, index + 1));
                }
            }
            None
        } else if let Some(add) = downcast::<&arith::Add>(is, data) {
            Some(Node::scalar(
                value(*add.lhs()).integer() + value(*add.rhs()).integer(),
            ))
        } else if let Some(lt) = downcast::<&cmp::Lt>(is, data) {
            Some(Node::scalar(u64::from(
                value(*lt.lhs()).integer() < value(*lt.rhs()).integer(),
            )))
        } else if let Some(jump) = downcast::<&control_flow::Jump>(is, data) {
            pending.push((*jump.dest(), Some(block), world, steps, 0));
            return;
        } else if let Some(branch) = downcast::<&control_flow::Br>(is, data) {
            let dest = if value(*branch.cond()).integer() != 0 {
                *branch.nz_dest()
            } else {
                *branch.z_dest()
            };
            pending.push((dest, Some(block), world, steps, 0));
            return;
        } else if let Some(branch) = downcast::<&control_flow::BrTable>(is, data) {
            let scrutinee = value(*branch.scrutinee()).integer();
            let dest = branch
                .table()
                .iter()
                .find(|(case, _)| value(*case).integer() == scrutinee)
                .map(|(_, dest)| *dest)
                .or(*branch.default());
            if let Some(dest) = dest {
                pending.push((dest, Some(block), world, steps, 0));
            }
            return;
        } else if downcast::<&control_flow::Return>(is, data).is_some() {
            execution.returned += 1;
            execution.max_objects = execution.max_objects.max(world.objects.len());
            return;
        } else if downcast::<&control_flow::Unreachable>(is, data).is_some() {
            return;
        } else {
            panic!("unsupported concrete instruction {inst:?}");
        };
        if let Some(output) = output {
            world.values.insert(
                func.dfg.inst_result(inst).expect("instruction result"),
                output,
            );
        }
    }
}
