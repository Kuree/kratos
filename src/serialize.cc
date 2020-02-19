#include "serialize.hh"
#include "cereal/types/polymorphic.hpp"

#include <cereal/archives/json.hpp>
#include <cereal/archives/binary.hpp>
#include <cereal/types/polymorphic.hpp>

// register base types
CEREAL_REGISTER_TYPE(kratos::IRNode)   // NOLINT
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::IRNode, kratos::Generator)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::IRNode, kratos::Var)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::IRNode, kratos::Stmt)

CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Var, kratos::Expr)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Var, kratos::Const)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Var, kratos::VarSlice)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Var, kratos::VarCasted)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::VarSlice, kratos::VarVarSlice)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Const, kratos::Param)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::VarSlice, kratos::PackedSlice)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Var, kratos::VarPackedStruct)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Expr, kratos::VarConcat)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Expr, kratos::VarExtend)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Expr, kratos::ConditionalExpr)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Const, kratos::EnumConst)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Var, kratos::EnumVar)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Var, kratos::FunctionCallVar)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Var, kratos::InterfaceVar)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Var, kratos::Port)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Port, kratos::EnumPort)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Port, kratos::PortPackedStruct)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Port, kratos::InterfacePort)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::InterfacePort, kratos::ModportPort)

CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Stmt, kratos::AssertPropertyStmt)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Stmt, kratos::AssertValueStmt)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Stmt, kratos::AssignStmt)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Stmt, kratos::IfStmt)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Stmt, kratos::SwitchStmt)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Stmt, kratos::StmtBlock)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::StmtBlock, kratos::ScopedStmtBlock)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::StmtBlock, kratos::CombinationalStmtBlock)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::StmtBlock, kratos::SequentialStmtBlock)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::StmtBlock, kratos::FunctionStmtBlock)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::StmtBlock, kratos::InitialStmtBlock)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Stmt, kratos::ReturnStmt)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Stmt, kratos::FunctionCallStmt)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Stmt, kratos::ModuleInstantiationStmt)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Stmt, kratos::InterfaceInstantiationStmt)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Stmt, kratos::CommentStmt)
CEREAL_REGISTER_POLYMORPHIC_RELATION(kratos::Stmt, kratos::RawStringStmt)


void serialize(std::ostream &ostream, std::shared_ptr<kratos::Context> context) {
    cereal::JSONOutputArchive o_archive(ostream);
    o_archive(context);
}

void serialize(std::ostream &ostream, std::shared_ptr<kratos::Generator> gen) {
    cereal::JSONOutputArchive o_archive(ostream);
    o_archive(gen);
}

//std::shared_ptr<Generator> load_generator(std::istream &istream) {
//    cereal::JSONInputArchive i_archive(istream);
//    std::shared_ptr<Generator> gen;
//    i_archive(gen);
//    return gen;
// }
