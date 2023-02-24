// https://web.archive.org/web/20221201043540/https://www-users.cs.york.ac.uk/cb25/main-pages/publications/ShannonThesis2006.pdf.2
// stack regions:
//   - evaluation (e-stack)
//   - parameters (p-stack)
//   - locals (l-stack)
//   - transfers (x-stack)
//   - rest

mod function;

pub use function::Function;
