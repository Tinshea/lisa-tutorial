package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.analysis.ScopeToken;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.lattices.SetLattice;
import it.unive.lisa.analysis.lattices.FunctionalLattice;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.program.cfg.statement.numeric.Addition;
import it.unive.lisa.program.cfg.statement.numeric.Subtraction;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.symbolic.value.operator.binary.*;
import it.unive.lisa.symbolic.SymbolicExpression;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class TwoVarLinearInequality extends FunctionalLattice<TwoVarLinearInequality, Identifier, TwoVarLinearInequality.SetOfInequalities>
        implements ValueDomain<TwoVarLinearInequality> {

    /**
     * Représente une inégalité linéaire de la forme : a*x + b*y ≤ c
     */
    public static class LinearInequality {
        private final Identifier var1; // x
        private final double coeff1;   // a
        private final Identifier var2; // y
        private final double coeff2;   // b
        private final double constant; // c

        public LinearInequality(Identifier var1, double coeff1, Identifier var2, double coeff2, double constant) {
            this.var1 = var1;
            this.coeff1 = coeff1;
            this.var2 = var2;
            this.coeff2 = coeff2;
            this.constant = constant;
        }

        public Identifier getVar1() { return var1; }
        public double getCoeff1() { return coeff1; }
        public Identifier getVar2() { return var2; }
        public double getCoeff2() { return coeff2; }
        public double getConstant() { return constant; }

        public Set<Identifier> getVariables() {
            Set<Identifier> vars = new HashSet<>();
            if (var1 != null && coeff1 != 0) vars.add(var1);
            if (var2 != null && coeff2 != 0) vars.add(var2);
            return vars;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) return true;
            if (obj == null || getClass() != obj.getClass()) return false;
            LinearInequality other = (LinearInequality) obj;
            return Double.compare(coeff1, other.coeff1) == 0 &&
                   Double.compare(coeff2, other.coeff2) == 0 &&
                   Double.compare(constant, other.constant) == 0 &&
                   Objects.equals(var1, other.var1) &&
                   Objects.equals(var2, other.var2);
        }

        @Override
        public int hashCode() {
            return Objects.hash(var1, coeff1, var2, coeff2, constant);
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
            boolean hasTerm = false;
            if (var1 != null && coeff1 != 0) {
                if (coeff1 != 1.0) sb.append(coeff1);
                sb.append(var1);
                hasTerm = true;
            }
            if (var2 != null && coeff2 != 0) {
                if (hasTerm) sb.append(coeff2 > 0 ? " + " : " - ");
                if (Math.abs(coeff2) != 1.0) sb.append(Math.abs(coeff2));
                sb.append(var2);
            }
            sb.append(" ≤ ").append(constant);
            return sb.toString();
        }
    }

    /**
     * Lattice représentant un ensemble d'inégalités linéaires
     */
    public static class SetOfInequalities extends SetLattice<SetOfInequalities, LinearInequality> {
        public SetOfInequalities(Set<LinearInequality> elements, boolean isTop) {
            super(elements, isTop);
        }

        @Override
        public SetOfInequalities mk(Set<LinearInequality> set) {
            return new SetOfInequalities(set, set.isEmpty());
        }

        @Override
        public SetOfInequalities top() {
            return new SetOfInequalities(Collections.emptySet(), true);
        }

        @Override
        public SetOfInequalities bottom() {
            return new SetOfInequalities(Collections.emptySet(), false);
        }
    }

    /**
     * Constructeurs de l’état abstrait
     */
    public TwoVarLinearInequality(SetOfInequalities lattice, Map<Identifier, SetOfInequalities> function) {
        super(lattice, function);
    }

    public TwoVarLinearInequality(SetOfInequalities lattice) {
        super(lattice);
    }

    public TwoVarLinearInequality() {
        super(new SetOfInequalities(Collections.emptySet(), true));
    }

    @Override
    public SetOfInequalities stateOfUnknown(Identifier id) {
        return new SetOfInequalities(Collections.emptySet(), true);
    }

    @Override
    public TwoVarLinearInequality mk(SetOfInequalities lattice, Map<Identifier, SetOfInequalities> function) {
        return new TwoVarLinearInequality(lattice, function);
    }

    public TwoVarLinearInequality top() {
        return new TwoVarLinearInequality(new SetOfInequalities(Collections.emptySet(), true), null);
    }

    public TwoVarLinearInequality bottom() {
        return new TwoVarLinearInequality(new SetOfInequalities(Collections.emptySet(), false), null);
    }

    @Override
    public boolean knowsIdentifier(Identifier identifier) {
        return this.getKeys().contains(identifier);
    }

    // ------------------------------
// Algorithme de fermeture (completion)
// ------------------------------

private Set<LinearInequality> close(Set<LinearInequality> inequalities) {
    Set<LinearInequality> current = new HashSet<>(inequalities);
    int iterations = Math.max(1, (int) Math.floor(Math.log(Math.max(1, getAllVars(inequalities).size() - 1)) / Math.log(2)));

    for (int i = 0; i < iterations; i++) {
        Set<LinearInequality> resultSet = result(current);
        current.addAll(resultSet);
        current = filter(current);
        if (containsContradiction(current))
            return current;
    }
    return current;
}

private Set<Identifier> getAllVars(Set<LinearInequality> ineqs) {
    Set<Identifier> vars = new HashSet<>();
    for (LinearInequality i : ineqs)
        vars.addAll(i.getVariables());
    return vars;
}

private boolean containsContradiction(Set<LinearInequality> set) {
    for (LinearInequality i : set)
        if (Math.abs(i.getCoeff1()) < 1e-10 && Math.abs(i.getCoeff2()) < 1e-10 && i.getConstant() < 0)
            return true;
    return false;
}

private Set<LinearInequality> result(Set<LinearInequality> ineqs) {
    Set<LinearInequality> res = new HashSet<>();
    for (LinearInequality t1 : ineqs) {
        for (LinearInequality t2 : ineqs) {
            if (t1 == t2) continue;
            if (!Objects.equals(t1.getVar2(), t2.getVar2())) continue;
            if (t1.getVar1() == null || t2.getVar1() == null) continue;

            double a = t1.getCoeff1(), b = t1.getCoeff2(), c = t1.getConstant();
            double d = t2.getCoeff1(), e = t2.getCoeff2(), f = t2.getConstant();

            if (a > 0 && d < 0) {
                double newCoeffZ = a * e;
                double newCoeffY = -d * b;
                double newConst = a * f - d * c;
                res.add(new LinearInequality(t1.getVar1(), newCoeffY, t1.getVar2(), newCoeffZ, newConst));
            }
        }
    }
    return res;
}

private Set<LinearInequality> filter(Set<LinearInequality> set) {
    for (LinearInequality i : set) {
        if (Math.abs(i.getCoeff1()) < 1e-10 && Math.abs(i.getCoeff2()) < 1e-10 && i.getConstant() < -1e-10)
            return Collections.singleton(i);
    }
    return new HashSet<>(set);
}

// ------------------------------
// Construction d'un domaine à partir d'inégalités
// ------------------------------

private TwoVarLinearInequality createDomainFromInequalities(Set<LinearInequality> inequalities) {
    TwoVarLinearInequality result = new TwoVarLinearInequality();
    for (LinearInequality ineq : inequalities) {
        for (Identifier var : ineq.getVariables()) {
            Set<LinearInequality> current = new HashSet<>(result.getState(var).elements);
            current.add(ineq);
            result = result.putState(var, new SetOfInequalities(current, false));
        }
    }
    return result;
}

// ------------------------------
// Analyse abstraite : assign()
// ------------------------------

@Override
public TwoVarLinearInequality assign(Identifier id, ValueExpression expr, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
    TwoVarLinearInequality result = this.forgetIdentifier(id);

    if (expr instanceof BinaryExpression be) {
        SymbolicExpression left = be.getLeft();
        SymbolicExpression right = be.getRight();
        BinaryOperator op = be.getOperator();

        if (op instanceof Addition || op instanceof Subtraction) {
            if (left instanceof Identifier var && right instanceof Constant c && c.getValue() instanceof Number) {
                double val = ((Number) c.getValue()).doubleValue();
                if (op instanceof Subtraction) val = -val;

                LinearInequality i1 = new LinearInequality(id, 1.0, var, -1.0, val);
                LinearInequality i2 = new LinearInequality(var, 1.0, id, -1.0, -val);
                Set<LinearInequality> set = new HashSet<>(List.of(i1, i2));
                result = createDomainFromInequalities(close(set));
            }
        }
    } else if (expr instanceof Identifier var) {
        LinearInequality i1 = new LinearInequality(id, 1.0, var, -1.0, 0.0);
        LinearInequality i2 = new LinearInequality(var, 1.0, id, -1.0, 0.0);
        Set<LinearInequality> set = new HashSet<>(List.of(i1, i2));
        result = createDomainFromInequalities(close(set));
    } else if (expr instanceof Constant c && c.getValue() instanceof Number) {
        double val = ((Number) c.getValue()).doubleValue();
        LinearInequality i1 = new LinearInequality(id, 1.0, null, 0.0, val);
        LinearInequality i2 = new LinearInequality(id, -1.0, null, 0.0, -val);
        Set<LinearInequality> set = new HashSet<>(List.of(i1, i2));
        result = createDomainFromInequalities(close(set));
    }

    return result;
}

// ------------------------------
// Analyse abstraite : assume()
// ------------------------------

@Override
public TwoVarLinearInequality assume(ValueExpression expr, ProgramPoint src, ProgramPoint dest, SemanticOracle oracle) throws SemanticException {
    if (!(expr instanceof BinaryExpression be)) return this;
    SymbolicExpression left = be.getLeft();
    SymbolicExpression right = be.getRight();
    BinaryOperator op = be.getOperator();

    TwoVarLinearInequality result = this;

    if (left instanceof Identifier x && right instanceof Identifier y) {
        if (op instanceof ComparisonLe || op instanceof ComparisonLt) {
            result = result.addInequality(new LinearInequality(x, 1.0, y, -1.0, 0.0));
        } else if (op instanceof ComparisonGe || op instanceof ComparisonGt) {
            result = result.addInequality(new LinearInequality(y, 1.0, x, -1.0, 0.0));
        } else if (op instanceof ComparisonEq) {
            result = result.addInequality(new LinearInequality(x, 1.0, y, -1.0, 0.0));
            result = result.addInequality(new LinearInequality(y, 1.0, x, -1.0, 0.0));
        }
    } else if (left instanceof Identifier x && right instanceof Constant c && c.getValue() instanceof Number val) {
        double v = val.doubleValue();
        if (op instanceof ComparisonLe || op instanceof ComparisonLt) {
            result = result.addInequality(new LinearInequality(x, 1.0, null, 0.0, v));
        } else if (op instanceof ComparisonGe || op instanceof ComparisonGt) {
            result = result.addInequality(new LinearInequality(x, -1.0, null, 0.0, -v));
        } else if (op instanceof ComparisonEq) {
            result = result.addInequality(new LinearInequality(x, 1.0, null, 0.0, v));
            result = result.addInequality(new LinearInequality(x, -1.0, null, 0.0, -v));
        }
    }

    return createDomainFromInequalities(close(getAllInequalities(result)));
}

private TwoVarLinearInequality addInequality(LinearInequality i) {
    Set<LinearInequality> updated = new HashSet<>(getAllInequalities(this));
    updated.add(i);
    return createDomainFromInequalities(close(updated));
}

private Set<LinearInequality> getAllInequalities(TwoVarLinearInequality d) {
    Set<LinearInequality> all = new HashSet<>();
    for (Identifier id : d.getKeys())
        all.addAll(d.getState(id).elements);
    return all;
}

// ------------------------------
// Entailment et lessOrEqual
// ------------------------------

@Override
public boolean lessOrEqual(TwoVarLinearInequality other) throws SemanticException {
    if (this.isBottom()) return true;
    if (other.isBottom()) return false;
    if (this.isTop()) return other.isTop();
    if (other.isTop()) return true;

    for (LinearInequality i : getAllInequalities(this))
        if (!entails(other, i))
            return false;

    return true;
}

private boolean entails(TwoVarLinearInequality system, LinearInequality ineq) {
    Set<LinearInequality> constraints = getAllInequalities(system);

    if (constraints.contains(ineq)) return true;

    for (LinearInequality known : constraints) {
        if (!Objects.equals(known.getVar1(), ineq.getVar1()) || !Objects.equals(known.getVar2(), ineq.getVar2()))
            continue;

        double a1 = ineq.getCoeff1(), b1 = ineq.getCoeff2(), c1 = ineq.getConstant();
        double a2 = known.getCoeff1(), b2 = known.getCoeff2(), c2 = known.getConstant();

        double det = a1 * b2 - a2 * b1;
        if (Math.abs(det) > 1e-10) return false;
        if (a1 * a2 < 0 || b1 * b2 < 0) return false;
        if (a1 != 0) return (a2 / a1) * c1 <= c2;
        if (b1 != 0) return (b2 / b1) * c1 <= c2;
        return c1 <= c2;
    }

    return false;
}

// ------------------------------
// Test de satisfiabilité
// ------------------------------

@Override
public Satisfiability satisfies(ValueExpression expr, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
    if (this.isBottom()) return Satisfiability.BOTTOM;
    if (!(expr instanceof BinaryExpression be)) return Satisfiability.UNKNOWN;

    SymbolicExpression left = be.getLeft();
    SymbolicExpression right = be.getRight();
    BinaryOperator op = be.getOperator();

    if (left instanceof Identifier x && right instanceof Identifier y) {
        for (LinearInequality i : getAllInequalities(this)) {
            if (op instanceof ComparisonLe || op instanceof ComparisonLt) {
                if (Objects.equals(i.getVar1(), x) && Objects.equals(i.getVar2(), y) && i.getCoeff1() == 1.0 && i.getCoeff2() == -1.0 && i.getConstant() <= 0)
                    return Satisfiability.SATISFIED;
            } else if (op instanceof ComparisonGe || op instanceof ComparisonGt) {
                if (Objects.equals(i.getVar1(), y) && Objects.equals(i.getVar2(), x) && i.getCoeff1() == 1.0 && i.getCoeff2() == -1.0 && i.getConstant() <= 0)
                    return Satisfiability.SATISFIED;
            } else if (op instanceof ComparisonEq) {
                boolean xLeY = constraintsContain(x, y, this);
                boolean yLeX = constraintsContain(y, x, this);
                if (xLeY && yLeX) return Satisfiability.SATISFIED;
            }
        }
    } else if (left instanceof Identifier x && right instanceof Constant c && c.getValue() instanceof Number) {
        double v = ((Number) c.getValue()).doubleValue();
        for (LinearInequality i : getAllInequalities(this)) {
            if (op instanceof ComparisonLe && i.getVar1().equals(x) && i.getVar2() == null && i.getCoeff1() == 1.0 && i.getConstant() <= v)
                return Satisfiability.SATISFIED;
            if (op instanceof ComparisonGe && i.getVar1().equals(x) && i.getVar2() == null && i.getCoeff1() == -1.0 && i.getConstant() <= -v)
                return Satisfiability.SATISFIED;
        }
    }

    return Satisfiability.UNKNOWN;
}

private boolean constraintsContain(Identifier x, Identifier y, TwoVarLinearInequality state) {
    for (LinearInequality i : getAllInequalities(state)) {
        if (Objects.equals(i.getVar1(), x) && Objects.equals(i.getVar2(), y) && i.getCoeff1() == 1.0 && i.getCoeff2() == -1.0 && i.getConstant() <= 0)
            return true;
    }
    return false;
}

// ------------------------------
// Oubli de variables
// ------------------------------

@Override
public TwoVarLinearInequality forgetIdentifier(Identifier identifier) throws SemanticException {
    TwoVarLinearInequality result = this;

    if (result.getKeys().contains(identifier)) {
        result = result.putState(identifier, new SetOfInequalities(Collections.emptySet(), true));
    }

    for (Identifier id : new HashSet<>(result.getKeys())) {
        Set<LinearInequality> updated = result.getState(id).elements.stream()
                .filter(i -> !i.getVariables().contains(identifier))
                .collect(Collectors.toSet());

        if (updated.size() != result.getState(id).elements.size()) {
            result = result.putState(id, new SetOfInequalities(updated, updated.isEmpty()));
        }
    }

    return result;
}

@Override
public TwoVarLinearInequality forgetIdentifiersIf(Predicate<Identifier> predicate) throws SemanticException {
    TwoVarLinearInequality result = this;
    for (Identifier id : this.getKeys()) {
        if (predicate.test(id)) {
            result = result.forgetIdentifier(id);
        }
    }
    return result;
}

@Override
public TwoVarLinearInequality pushScope(ScopeToken token) throws SemanticException {
    return this;
}

@Override
public TwoVarLinearInequality popScope(ScopeToken token) throws SemanticException {
    return this;
}

@Override
public StructuredRepresentation representation() {
    StringBuilder sb = new StringBuilder();

    Set<Identifier> allVars = new HashSet<>();
    for (Identifier id : this.getKeys()) {
        Set<LinearInequality> inequalities = this.getState(id).elements;
        for (LinearInequality ineq : inequalities) {
            allVars.addAll(ineq.getVariables());
        }
        allVars.add(id);
    }

    List<Identifier> sortedIds = new ArrayList<>(allVars);
    sortedIds.sort(Comparator.comparing(Identifier::getName));

    for (Identifier id : sortedIds) {
        sb.append(id.getName()).append(" → {\n");
        Set<LinearInequality> inequalities = this.getState(id).elements;

        if (inequalities == null || inequalities.isEmpty()) {
            sb.append("  (aucune contrainte)\n");
        } else {
            for (LinearInequality ineq : inequalities) {
                sb.append("  ").append(ineq.toString()).append("\n");
            }
        }
        sb.append("}\n");
    }

    return new StringRepresentation(sb.toString());
}

// ------------------------------
// Least Upper Bound (lub) avec fermeture
// ------------------------------

@Override
public TwoVarLinearInequality lub(TwoVarLinearInequality other) throws SemanticException {
    if (this.isBottom()) return other;
    if (other.isBottom()) return this;
    if (this.isTop() || other.isTop()) return top();

    Set<LinearInequality> combined = new HashSet<>();
    for (Identifier id : this.getKeys())
        combined.addAll(this.getState(id).elements);
    for (Identifier id : other.getKeys())
        combined.addAll(other.getState(id).elements);

    Set<LinearInequality> closure = close(combined);
    return createDomainFromInequalities(closure);
}

@Override
public TwoVarLinearInequality smallStepSemantics(ValueExpression expression, ProgramPoint pp, SemanticOracle oracle)
        throws SemanticException {
        return this;
}
}