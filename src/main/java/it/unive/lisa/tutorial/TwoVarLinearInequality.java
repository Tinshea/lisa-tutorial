package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.ScopeToken;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLe;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

import java.util.*;
import java.util.function.Predicate;

public class TwoVarLinearInequality implements ValueDomain<TwoVarLinearInequality> {

    private final Set<TwoVarsInequality> constraints;
    private final boolean topFlag, bottomFlag;

    public TwoVarLinearInequality() {
        this.constraints = new HashSet<>();
        this.topFlag = false;
        this.bottomFlag = false;
    }

    private TwoVarLinearInequality(boolean isTop, boolean isBottom, Set<TwoVarsInequality> constraints) {
        this.constraints = new HashSet<>(constraints);
        this.topFlag = isTop;
        this.bottomFlag = isBottom;
    }

    public static TwoVarLinearInequality mkTop() {
        return new TwoVarLinearInequality(true, false, Collections.emptySet());
    }

    public static TwoVarLinearInequality mkBottom() {
        return new TwoVarLinearInequality(false, true, Collections.emptySet());
    }

    @Override
    public TwoVarLinearInequality top() {
        return mkTop();
    }

    @Override
    public TwoVarLinearInequality bottom() {
        return mkBottom();
    }

    @Override
    public boolean isTop() {
        return topFlag;
    }

    @Override
    public boolean isBottom() {
        return bottomFlag;
    }

    @Override
    public TwoVarLinearInequality lub(TwoVarLinearInequality other) throws SemanticException {
        if (this.topFlag || other.topFlag) return mkTop();
        if (this.bottomFlag) return other;
        if (other.bottomFlag) return this;

        Set<TwoVarsInequality> union = new HashSet<>(this.constraints);
        union.addAll(other.constraints);
        return new TwoVarLinearInequality(false, false, union);
    }

    @Override
    public TwoVarLinearInequality glb(TwoVarLinearInequality other) throws SemanticException {
        if (this.bottomFlag || other.bottomFlag) return mkBottom();
        if (this.topFlag) return other;
        if (other.topFlag) return this;

        Set<TwoVarsInequality> intersection = new HashSet<>(this.constraints);
        intersection.retainAll(other.constraints);
        return new TwoVarLinearInequality(false, false, intersection);
    }

    @Override
    public boolean lessOrEqual(TwoVarLinearInequality other) throws SemanticException {
        return other.constraints.containsAll(this.constraints);
    }

    @Override
    public TwoVarLinearInequality assign(Identifier id, ValueExpression expression, ProgramPoint pp, SemanticOracle oracle)
            throws SemanticException {
        if (isBottom() || isHeapIdentifier(id)) return this;

        Set<TwoVarsInequality> newConstraints = new HashSet<>();

        if (expression instanceof Identifier otherId && !isHeapIdentifier(otherId)) {
            newConstraints.add(new TwoVarsInequality(1, id, -1, otherId, 0));
            newConstraints.add(new TwoVarsInequality(-1, id, 1, otherId, 0));
        } else if (expression instanceof BinaryExpression bin &&
                bin.getOperator() instanceof AdditionOperator &&
                bin.getLeft() instanceof Identifier left &&
                bin.getRight() instanceof Constant c &&
                c.getValue() instanceof Integer val && !isHeapIdentifier(left)) {
            newConstraints.add(new TwoVarsInequality(1, id, -1, left, val));
            newConstraints.add(new TwoVarsInequality(-1, id, 1, left, -val));
        }

        Set<TwoVarsInequality> all = new HashSet<>(this.constraints);
        all.addAll(newConstraints);
        return new TwoVarLinearInequality(false, false, all);
    }

    @Override
    public TwoVarLinearInequality smallStepSemantics(ValueExpression expr, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        return this;
    }

    @Override
    public TwoVarLinearInequality assume(ValueExpression expr, ProgramPoint src, ProgramPoint dest, SemanticOracle oracle) throws SemanticException {
        if (!(expr instanceof BinaryExpression bin) || !(bin.getOperator() instanceof ComparisonLe))
            return this;

        ValueExpression left = (ValueExpression) bin.getLeft();
        ValueExpression right = (ValueExpression) bin.getRight();

        if (left instanceof BinaryExpression addExpr && addExpr.getOperator() instanceof AdditionOperator
            && addExpr.getLeft() instanceof BinaryExpression mult1 && addExpr.getRight() instanceof BinaryExpression mult2
            && mult1.getOperator() instanceof it.unive.lisa.symbolic.value.operator.MultiplicationOperator
            && mult2.getOperator() instanceof it.unive.lisa.symbolic.value.operator.MultiplicationOperator
            && mult1.getLeft() instanceof Constant c1 && mult2.getLeft() instanceof Constant c2
            && mult1.getRight() instanceof Identifier x && mult2.getRight() instanceof Identifier y
            && right instanceof Constant c) {

            int a = (Integer) c1.getValue();
            int b = (Integer) c2.getValue();
            int d = (Integer) c.getValue();
            TwoVarsInequality ineq = new TwoVarsInequality(a, x, b, y, d);

            Set<TwoVarsInequality> newSet = new HashSet<>(constraints);
            newSet.add(ineq);
            return new TwoVarLinearInequality(false, false, newSet);
        }

        return this;
    }

    @Override
    public boolean knowsIdentifier(Identifier id) {
        for (TwoVarsInequality i : constraints) {
            if ((i.x != null && i.x.equals(id)) || (i.y != null && i.y.equals(id))) return true;
        }
        return false;
    }

    @Override
    public TwoVarLinearInequality forgetIdentifier(Identifier id) throws SemanticException {
        Set<TwoVarsInequality> newSet = new HashSet<>();
        for (TwoVarsInequality i : constraints) {
            if (!(id.equals(i.x) || id.equals(i.y))) newSet.add(i);
        }
        return new TwoVarLinearInequality(false, false, newSet);
    }

    @Override
    public TwoVarLinearInequality forgetIdentifiersIf(Predicate<Identifier> pred) throws SemanticException {
        Set<TwoVarsInequality> newSet = new HashSet<>();
        for (TwoVarsInequality i : constraints) {
            if ((i.x == null || !pred.test(i.x)) && (i.y == null || !pred.test(i.y))) newSet.add(i);
        }
        return new TwoVarLinearInequality(false, false, newSet);
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
    public Satisfiability satisfies(ValueExpression expr, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        return Satisfiability.UNKNOWN;
    }

    @Override
    public StructuredRepresentation representation() {
        if (topFlag) return new StringRepresentation("TOP");
        if (bottomFlag) return new StringRepresentation("BOTTOM");
        return new StringRepresentation(constraints.toString());
    }

    public static boolean isHeapIdentifier(Identifier id) {
        if (id == null) return false;
        String s = id.toString();
        return s.contains("heap") || s.contains("this") || s.contains("&pp@");
    }

    public static class TwoVarsInequality {
        public final int a, b, c;
        public final Identifier x, y;

        public TwoVarsInequality(int a, Identifier x, int b, Identifier y, int c) {
            this.a = a;
            this.b = b;
            this.c = c;
            this.x = x;
            this.y = y;
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
            if (a != 0 && x != null) sb.append(a).append("*").append(x);
            if (b > 0 && y != null) sb.append(" + ").append(b).append("*").append(y);
            else if (b < 0 && y != null) sb.append(" - ").append(-b).append("*").append(y);
            sb.append(" <= ").append(c);
            return sb.toString();
        }

        @Override
        public boolean equals(Object obj) {
            if (!(obj instanceof TwoVarsInequality other)) return false;
            return a == other.a && b == other.b && c == other.c && Objects.equals(x, other.x) && Objects.equals(y, other.y);
        }

        @Override
        public int hashCode() {
            return Objects.hash(a, b, c, x, y);
        }
    }
}
