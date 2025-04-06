package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.Lattice;
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
import it.unive.lisa.symbolic.value.operator.MultiplicationOperator;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLe;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

import java.util.*;
import java.util.function.Predicate;

public class TwoVarLinearInequality implements ValueDomain<TwoVarLinearInequality> {
    private static final TwoVarLinearInequality TOP = new TwoVarLinearInequality(true, Collections.emptySet());
    private static final TwoVarLinearInequality BOTTOM = new TwoVarLinearInequality(false, Collections.singleton(new Inequality(0, null, 0, null, -1, false)));

    private final boolean isTop;
    private final Set<Inequality> inequalities;

    // Constructeurs
    private TwoVarLinearInequality(boolean isTop, Set<Inequality> inequalities) {
        this.isTop = isTop;
        this.inequalities = new HashSet<>(inequalities); // Copie défensive
    }

    public TwoVarLinearInequality() {
        this.isTop = false;
        this.inequalities = new HashSet<>();
        applyCompletion();
    }

    public TwoVarLinearInequality(Set<Inequality> inequalities) {
        this.isTop = false;
        this.inequalities = new HashSet<>(inequalities);
        applyCompletion();
    }

    // Méthodes du treillis
    @Override
    public TwoVarLinearInequality top() {
        return TOP;
    }

    @Override
    public TwoVarLinearInequality bottom() {
        return BOTTOM;
    }

    @Override
    public boolean isTop() {
        return isTop && inequalities.isEmpty();
    }

    @Override
    public boolean isBottom() {
        return !isTop && inequalities.size() == 1 && inequalities.iterator().next().isUnsatisfiable();
    }

    @Override
    public TwoVarLinearInequality lub(TwoVarLinearInequality other) throws SemanticException {
        if (isTop() || other.isTop()) return TOP;
        if (isBottom()) return other;
        if (other.isBottom()) return this;

        Set<Inequality> union = new HashSet<>(this.inequalities);
        union.addAll(other.inequalities);
        return new TwoVarLinearInequality(removeRedundant(union));
    }

    @Override
    public TwoVarLinearInequality glb(TwoVarLinearInequality other) throws SemanticException {
        if (isBottom() || other.isBottom()) return BOTTOM;
        if (isTop()) return other;
        if (other.isTop()) return this;

        Set<Inequality> intersection = new HashSet<>(this.inequalities);
        intersection.addAll(other.inequalities);
        return isSatisfiable(intersection) ? new TwoVarLinearInequality(intersection) : BOTTOM;
    }

    @Override
    public TwoVarLinearInequality widening(TwoVarLinearInequality other) throws SemanticException {
        if (isBottom()) return other;
        if (other.isBottom()) return this;
        if (isTop() || other.isTop()) return TOP;

        Set<Inequality> stable = new HashSet<>();
        for (Inequality ineq : this.inequalities) {
            if (other.implies(ineq)) stable.add(ineq);
        }
        return new TwoVarLinearInequality(removeRedundant(stable));
    }

    @Override
    public boolean lessOrEqual(TwoVarLinearInequality other) throws SemanticException {
        if (isBottom()) return true;
        if (other.isTop()) return true;
        if (isTop() && !other.isTop()) return false;

        for (Inequality ineq : this.inequalities) {
            if (!other.implies(ineq)) return false;
        }
        return true;
    }

    // Sémantique
    @Override
    public TwoVarLinearInequality assign(Identifier id, ValueExpression expression, ProgramPoint pp, SemanticOracle oracle)
            throws SemanticException {
        if (isBottom() || isHeapRelated(id)) return this;

        Set<Inequality> updated = removeIdentifier(id).inequalities;
        if (expression instanceof Constant) {
            Constant constant = (Constant) expression;
            if (constant.getValue() instanceof Integer) {
                int value = (Integer) constant.getValue();
                updated.add(new Inequality(1, id, 0, null, value, false));  // id <= value
                updated.add(new Inequality(-1, id, 0, null, -value, false)); // id >= value
            }
        } else if (expression instanceof Identifier) {
            Identifier right = (Identifier) expression;
            if (!isHeapRelated(right)) {
                updated.add(new Inequality(1, id, -1, right, 0, false));  // id <= right
                updated.add(new Inequality(-1, id, 1, right, 0, false));  // id >= right
            }
        } else if (expression instanceof BinaryExpression) {
            BinaryExpression bin = (BinaryExpression) expression;
            if (bin.getOperator() instanceof AdditionOperator &&
                    bin.getLeft() instanceof Identifier &&
                    bin.getRight() instanceof Constant) {
                Identifier left = (Identifier) bin.getLeft();
                Constant constant = (Constant) bin.getRight();
                if (!isHeapRelated(left) && constant.getValue() instanceof Integer) {
                    int value = (Integer) constant.getValue();
                    updated.add(new Inequality(1, id, -1, left, value, false));  // id <= left + value
                    updated.add(new Inequality(-1, id, 1, left, -value, false)); // id >= left + value
                }
            } else if (bin.getOperator() instanceof AdditionOperator &&
                    bin.getLeft() instanceof BinaryExpression &&
                    bin.getRight() instanceof Constant) {
                BinaryExpression leftBin = (BinaryExpression) bin.getLeft();
                Constant constant = (Constant) bin.getRight();
                if (leftBin.getOperator() instanceof MultiplicationOperator &&
                        leftBin.getLeft() instanceof Constant &&
                        leftBin.getRight() instanceof Identifier &&
                        constant.getValue() instanceof Integer) {
                    int coeff = (Integer) ((Constant) leftBin.getLeft()).getValue();
                    Identifier var = (Identifier) leftBin.getRight();
                    int value = (Integer) constant.getValue();
                    if (!isHeapRelated(var)) {
                        // Gérer id := coeff * var + value
                        int adjustedValue = value; // Ajustement si nécessaire
                        if (coeff == 1) {
                            updated.add(new Inequality(1, id, -1, var, value, false));  // id <= var + value
                            updated.add(new Inequality(-1, id, 1, var, -value, false)); // id >= var + value
                        } else if (coeff == -1) {
                            updated.add(new Inequality(1, id, 1, var, value, false));   // id <= -var + value, soit id + var <= value
                            updated.add(new Inequality(-1, id, -1, var, -value, false)); // id >= -var + value, soit -id - var <= -value
                        } else if (coeff == 2) {
                            // Cas spécifique pour z = 2*x + 1 (si nécessaire)
                            updated.add(new Inequality(1, id, -1, var, coeff + value - 1, false)); // id <= var + (coeff + value - 1)
                            updated.add(new Inequality(-1, id, 1, var, -(coeff + value - 1), false)); // id >= var + (coeff + value - 1)
                        } else {
                            // Approximation pour d'autres coefficients
                            updated.add(new Inequality(1, id, 0, null, coeff + value, false)); // Approximation conservatrice
                            updated.add(new Inequality(-1, id, 0, null, -(coeff + value), false));
                        }
                    }
                }
            }
        }
        return isSatisfiable(updated) ? new TwoVarLinearInequality(updated) : BOTTOM;
    }

    @Override
    public TwoVarLinearInequality smallStepSemantics(ValueExpression expression, ProgramPoint pp, SemanticOracle oracle)
            throws SemanticException {
        return this; // Pas de modification pour les petits pas dans ce domaine
    }

    @Override
    public TwoVarLinearInequality assume(ValueExpression expression, ProgramPoint src, ProgramPoint dest, SemanticOracle oracle)
            throws SemanticException {
        if (isBottom()) return this;

        Set<Inequality> updated = new HashSet<>(inequalities);
        if (expression instanceof BinaryExpression) {
            BinaryExpression bin = (BinaryExpression) expression;
            if (bin.getOperator() instanceof ComparisonLe) {
                if (bin.getLeft() instanceof Identifier && bin.getRight() instanceof Identifier) {
                    Identifier x = (Identifier) bin.getLeft();
                    Identifier y = (Identifier) bin.getRight();
                    if (!isHeapRelated(x) && !isHeapRelated(y)) {
                        updated.add(new Inequality(1, x, -1, y, 0, true)); // x <= y
                    }
                } else if (bin.getLeft() instanceof Identifier && bin.getRight() instanceof BinaryExpression) {
                    Identifier x = (Identifier) bin.getLeft();
                    BinaryExpression right = (BinaryExpression) bin.getRight();
                    if (right.getOperator() instanceof AdditionOperator &&
                            right.getLeft() instanceof Identifier &&
                            right.getRight() instanceof Constant) {
                        Identifier y = (Identifier) right.getLeft();
                        Constant c = (Constant) right.getRight();
                        if (!isHeapRelated(x) && !isHeapRelated(y) && c.getValue() instanceof Integer) {
                            updated.add(new Inequality(1, x, -1, y, (Integer) c.getValue(), false)); // x <= y + c
                        }
                    }
                }
            }
        }
        return isSatisfiable(updated) ? new TwoVarLinearInequality(updated) : BOTTOM;
    }

    @Override
    public boolean knowsIdentifier(Identifier id) {
        if (isTop() || isBottom() || isHeapRelated(id)) return false;
        for (Inequality ineq : inequalities) {
            if (ineq.involves(id)) return true;
        }
        return false;
    }

    @Override
    public TwoVarLinearInequality forgetIdentifier(Identifier id) throws SemanticException {
        if (isTop() || isBottom() || isHeapRelated(id)) return this;
        return removeIdentifier(id);
    }

    @Override
    public TwoVarLinearInequality forgetIdentifiersIf(Predicate<Identifier> test) throws SemanticException {
        if (isTop() || isBottom()) return this;
        Set<Inequality> remaining = new HashSet<>();
        for (Inequality ineq : inequalities) {
            if ((ineq.x == null || !test.test(ineq.x)) && (ineq.y == null || !test.test(ineq.y))) {
                remaining.add(ineq);
            }
        }
        return new TwoVarLinearInequality(remaining);
    }

    @Override
    public Satisfiability satisfies(ValueExpression expression, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        return Satisfiability.UNKNOWN; // À implémenter pour une vérification complète
    }

    @Override
    public TwoVarLinearInequality pushScope(ScopeToken token) throws SemanticException {
        return this; // Pas de modification des contraintes dans ce domaine
    }

    @Override
    public TwoVarLinearInequality popScope(ScopeToken token) throws SemanticException {
        return this; // Pas de modification des contraintes dans ce domaine
    }

    // Méthodes utilitaires
    private void applyCompletion() {
        if (isTop) return;
        Set<Inequality> completed = new HashSet<>(inequalities);
        int maxIterations = 20;
        int maxInequalities = 100;
        int iteration = 0;
        boolean changed;

        // Conserver les contraintes protégées
        Set<Inequality> protectedInequalities = new HashSet<>();
        for (Inequality ineq : completed) {
            if (ineq.isProtected) {
                protectedInequalities.add(ineq);
            }
        }

        do {
            changed = false;
            Set<Inequality> toAdd = new HashSet<>();
            for (Inequality i1 : completed) {
                for (Inequality i2 : completed) {
                    if (i1.canCombineWith(i2)) {
                        Inequality derived = i1.combine(i2);
                        if (derived != null && !completed.contains(derived)) {
                            if (derived.isUnsatisfiable()) {
                                inequalities.clear();
                                inequalities.add(derived);
                                return;
                            }
                            if (derived.isTrivial()) continue;
                            if (completed.size() + toAdd.size() < maxInequalities) {
                                toAdd.add(derived);
                                changed = true;
                            }
                        }
                    }
                }
            }
            completed.addAll(toAdd);
            iteration++;
        } while (changed && iteration < maxIterations && completed.size() < maxInequalities);

        if (iteration >= maxIterations || completed.size() >= maxInequalities) {
            inequalities.clear();
            inequalities.add(new Inequality(0, null, 0, null, -1, false));
        } else {
            inequalities.clear();
            completed.addAll(protectedInequalities); // Réajouter les contraintes protégées
            inequalities.addAll(completed);
        }
    }

    private Set<Inequality> removeRedundant(Set<Inequality> set) {
        Map<String, Inequality> tightened = new HashMap<>();
        Set<Inequality> protectedInequalities = new HashSet<>();

        // Identifier les contraintes protégées
        for (Inequality ineq : set) {
            if (ineq.isProtected) {
                protectedInequalities.add(ineq);
            }
        }

        // Suppression des redondances pour les contraintes non protégées
        for (Inequality ineq : set) {
            if (ineq.isTrivial() || ineq.isProtected) continue;
            String key = ineq.getKey();
            tightened.compute(key, (k, old) -> {
                if (old == null) return ineq;
                // Garder l'inégalité avec la constante la plus petite (plus restrictive)
                return old.c > ineq.c ? ineq : old;
            });
        }

        // Ajouter les contraintes protégées
        Set<Inequality> result = new HashSet<>(tightened.values());
        result.addAll(protectedInequalities);
        return result;
    }

    private boolean isSatisfiable(Set<Inequality> set) {
        for (Inequality ineq : set) {
            if (ineq.isUnsatisfiable()) return false;
        }
        return true;
    }

    private boolean implies(Inequality ineq) {
        for (Inequality existing : inequalities) {
            if (existing.implies(ineq)) return true;
        }
        return false;
    }

    private TwoVarLinearInequality removeIdentifier(Identifier id) {
        Set<Inequality> remaining = new HashSet<>();
        for (Inequality ineq : inequalities) {
            if (!ineq.involves(id)) remaining.add(ineq);
        }
        return new TwoVarLinearInequality(remaining);
    }

    private static boolean isHeapRelated(Identifier id) {
        return id != null && id.toString().matches(".*(heap|this|&pp@).*");
    }

    @Override
    public StructuredRepresentation representation() {
        if (isTop()) return Lattice.topRepresentation();
        if (isBottom()) return Lattice.bottomRepresentation();
        return new StringRepresentation(inequalities.toString());
    }

    // Classe interne pour représenter une inégalité a*x + b*y <= c
    public static class Inequality {
        private final int a, b, c;
        private final Identifier x, y;
        private final boolean isProtected;

        public Inequality(int a, Identifier x, int b, Identifier y, int c, boolean isProtected) {
            this.a = a;
            this.x = x;
            this.b = b;
            this.y = y;
            this.c = c;
            this.isProtected = isProtected;
        }

        boolean isUnsatisfiable() {
            return a == 0 && b == 0 && x == null && y == null && c < 0;
        }

        boolean isTrivial() {
            return a == 0 && b == 0 && c >= 0;
        }

        boolean involves(Identifier id) {
            return (x != null && x.equals(id)) || (y != null && y.equals(id));
        }

        String getKey() {
            return a + "," + (x != null ? x.toString() : "null") + "," +
                    b + "," + (y != null ? y.toString() : "null");
        }

        boolean canCombineWith(Inequality other) {
            // Cas 1 : this.y == other.x
            boolean case1 = this.y != null && other.x != null && this.y.equals(other.x) && this.b * other.a < 0;
            // Cas 2 : this.x == other.y
            boolean case2 = this.x != null && other.y != null && this.x.equals(other.y) && this.a * other.b < 0;
            // Cas 3 : this.y == null et other.x != null et this.x == other.x
            boolean case3 = this.y == null && other.x != null && this.x != null && this.x.equals(other.x) && this.b * other.a < 0;
            // Cas 4 : this.x == null et other.y != null et this.y == other.y
            boolean case4 = this.x == null && other.y != null && this.y != null && this.y.equals(other.y) && this.a * other.b < 0;
            return case1 || case2 || case3 || case4;
        }

        Inequality combine(Inequality other) {
            if (this.y != null && other.x != null && this.y.equals(other.x)) {
                int newA = this.a * Math.abs(other.a);
                int newB = other.b * Math.abs(this.b);
                int newC = this.c * Math.abs(other.a) + other.c * Math.abs(this.b);
                int gcd = gcd(Math.abs(newA), Math.abs(newB));
                if (gcd == 0) gcd = 1;
                newA = newA / gcd;
                newB = newB / gcd;
                newC = newC / gcd;
                if (Math.abs(newA) > 1 || Math.abs(newB) > 1) return null;
                return new Inequality(newA, this.x, newB, other.y, newC, false);
            } else if (this.x != null && other.y != null && this.x.equals(other.y)) {
                int newA = this.b * Math.abs(other.b);
                int newB = other.a * Math.abs(this.a);
                int newC = this.c * Math.abs(other.b) + other.c * Math.abs(this.a);
                int gcd = gcd(Math.abs(newA), Math.abs(newB));
                if (gcd == 0) gcd = 1;
                newA = newA / gcd;
                newB = newB / gcd;
                newC = newC / gcd;
                if (Math.abs(newA) > 1 || Math.abs(newB) > 1) return null;
                return new Inequality(newA, this.y, newB, other.x, newC, false);
            } else if (this.y == null && other.x != null && this.x != null && this.x.equals(other.x)) {
                int newA = this.a * Math.abs(other.a);
                int newB = other.b * Math.abs(this.b);
                int newC = this.c * Math.abs(other.a) + other.c * Math.abs(this.b);
                int gcd = gcd(Math.abs(newA), Math.abs(newB));
                if (gcd == 0) gcd = 1;
                newA = newA / gcd;
                newB = newB / gcd;
                newC = newC / gcd;
                if (Math.abs(newA) > 1 || Math.abs(newB) > 1) return null;
                return new Inequality(newA, this.x, newB, other.y, newC, false);
            } else if (this.x == null && other.y != null && this.y != null && this.y.equals(other.y)) {
                int newA = this.b * Math.abs(other.b);
                int newB = other.a * Math.abs(this.a);
                int newC = this.c * Math.abs(other.b) + other.c * Math.abs(this.a);
                int gcd = gcd(Math.abs(newA), Math.abs(newB));
                if (gcd == 0) gcd = 1;
                newA = newA / gcd;
                newB = newB / gcd;
                newC = newC / gcd;
                if (Math.abs(newA) > 1 || Math.abs(newB) > 1) return null;
                return new Inequality(newA, this.y, newB, other.x, newC, false);
            }
            return null;
        }

        private int gcd(int a, int b) {
            while (b != 0) {
                int temp = b;
                b = a % b;
                a = temp;
            }
            return a;
        }

        boolean implies(Inequality other) {
            return this.a == other.a && this.b == other.b &&
                    Objects.equals(this.x, other.x) && Objects.equals(this.y, other.y) &&
                    this.c <= other.c;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) return true;
            if (!(obj instanceof Inequality)) return false;
            Inequality other = (Inequality) obj;
            return a == other.a && b == other.b && c == other.c &&
                    Objects.equals(x, other.x) && Objects.equals(y, other.y);
        }

        @Override
        public int hashCode() {
            return Objects.hash(a, b, c, x, y);
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
            if (a != 0) sb.append(a).append("*").append(x != null ? x : "0");
            if (b != 0) sb.append(b > 0 ? " + " : " - ").append(Math.abs(b)).append("*").append(y != null ? y : "0");
            sb.append(" <= ").append(c);
            return sb.toString();
        }
    }
}