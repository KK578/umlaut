const REGEX_UUID = /[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}/i;

const testee = require('../../uml-parser/util/classes.js');
let TestClass;

describe('UML Parser Classes', function () {
	describe('AnnotatedUmlClass', function () {
		before(function () {
			TestClass = testee.AnnotatedUmlClass;
		});

		it('should error on empty input', function () {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should take a name', function () {
			const obj = new TestClass('foo');

			// expect(obj.id).to.be.a('string').and.not.equal('');
			expect(obj.name).to.equal('foo');
		});

		it('should define data structures after initialisation', function () {
			const obj = new TestClass('foo');

			expect(obj.variables).to.be.an('object');
			expect(obj.methods).to.be.an('object');
			expect(obj.invariants).to.be.instanceOf(Array);
		});

		describe('#addVariable', function () {
			let obj;

			beforeEach(function () {
				obj = new TestClass('foo');
			});

			it('should error on empty input', function () {
				expect(obj.addVariable).to.throw(Error);
			});

			it('should take a name', function () {
				obj.addVariable('a');

				expect(obj.variables).to.include.keys('a');
				expect(obj.variables['a']).to.include({ type: 'object' });
			});

			it('should take a name and type', function () {
				obj.addVariable('a', 'Integer');

				expect(obj.variables).to.include.keys('a');
				expect(obj.variables['a']).to.include({ type: 'Integer' });
			});

			it('should error if variable name already exists', function () {
				obj.addVariable('a', 'Integer');

				expect(obj.variables).to.include.keys('a');
				expect(obj.variables['a']).to.include({ type: 'Integer' });

				expect(obj.addVariable.bind(obj, 'a', 'Integer')).to.throw(Error);
			});
		});

		describe('#addMethod', function () {
			let obj;

			beforeEach(function () {
				obj = new TestClass('foo');
			});

			it('should error on empty input', function () {
				expect(obj.addMethod).to.throw(Error);
			});

			it('should error with just name', function () {
				expect(obj.addMethod.bind(obj, 'foo')).to.throw(Error);
			});

			it('should take a name and type', function () {
				const methodsLength = Object.keys(obj.methods).length;

				obj.addMethod('foo', 'Integer');

				expect(Object.keys(obj.methods).length).to.equal(methodsLength + 1);
				expect(obj.methods).to.include.keys('foo');
			});

			it('should take a name and type and list of arguments', function () {
				obj.addMethod('foo', 'Integer', [{ a: { type: 'Integer' } }]);

				expect(obj.methods).to.include.keys('foo');
				expect(obj.methods['foo'].type).equal('Integer');
				expect(obj.methods['foo'].arguments).to.include({ a: { type: 'Integer' } });
			});

			it('should error if list of arguments is not an Array', function () {
				expect(obj.addMethod.bind(obj, 'foo', 'Integer', 'a')).to.throw(Error);
			});

			it('should error if method name already exists', function () {
				obj.addMethod('foo', 'Integer');

				// Validate method is added.
				expect(obj.methods).to.include.keys('foo');

				// Test adding method again.
				expect(obj.addMethod.bind(obj, 'foo', 'Integer')).to.throw(Error);
			});
		});

		describe('#addInvariant', function () {
			let obj;

			beforeEach(function () {
				obj = new TestClass('foo');
			});

			it('should error on empty', function () {
				expect(obj.addInvariant).to.throw(Error);
			});

			it('should error if argument is not an object', function () {
				expect(obj.addInvariant.bind(obj, '(> a b)')).to.throw(Error);
			});

			it('should add a new invariant', function () {
				const invariantLength = obj.invariants.length;

				obj.addInvariant({
					comparison: 'LessThan',
					arguments: [
						'a',
						'b'
					]
				});

				expect(obj.invariants.length).to.equal(invariantLength + 1);
			});

			it('should error if invariant object does not specify the comparison', function () {
				expect(obj.addInvariant.bind(obj, {
					comparison: undefined,
					arguments: [
						'a',
						'b'
					]
				})).to.throw(Error);
			});

			it('should error if invariant object does not specify at least 1 item in arguments', function () {
				expect(obj.addInvariant.bind(obj, {
					comparison: 'LessThan',
					arguments: []
				})).to.throw(Error);
			});

			it('should generate a unique ID for the condition');
		});
	});

	describe('UmlAnnotatedMethod', function () {
		before(function () {
			TestClass = testee.AnnotatedUmlMethod;
		});

		it('should error on empty input', function () {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should error with just name', function () {
			expect(() => {
				new TestClass('foo');
			}).to.throw(Error);
		});

		it('should take a name and type', function () {
			const obj = new TestClass('foo', 'Integer');

			expect(obj.name).to.equal('foo');
			expect(obj.type).to.equal('Integer');
		});

		it('should take a name and type and list of arguments', function () {
			const obj = new TestClass('foo', 'Integer', [{ a: { type: 'Integer' } }]);

			expect(obj.name).to.equal('foo');
			expect(obj.type).to.equal('Integer');
			expect(obj.arguments).to.include({ a: { type: 'Integer' } });
		});

		it('should error if list of arguments is not an array', function () {
			expect(() => {
				new TestClass('foo', 'Integer', 'a');
			}).to.throw(Error);
		});

		it('should define hashmaps after initialisation', function () {
			const obj = new TestClass('foo', 'Integer');

			expect(obj.preconditions).to.be.an('object');
			expect(obj.postconditions).to.be.an('object');
		});

		describe('#setType', function () {
			let obj;

			beforeEach(function () {
				obj = new TestClass('foo', 'Integer');
			});

			it('should error on empty', function () {
				expect(obj.setType).to.throw(Error);
			});

			it('should take a type name', function () {
				expect(obj.type).to.not.equal('String');

				obj.setType('String');

				expect(obj.type).to.equal('String');
			});
		});

		describe('#addArgument', function () {
			let obj;

			beforeEach(function () {
				obj = new TestClass('foo', 'Integer');
			});

			it('should error on empty', function () {
				expect(obj.addArgument).to.throw(Error);
			});

			it('should add a new argument, as an object', function () {
				obj.addArgument({
					name: 'a',
					type: 'Integer'
				});

				expect(obj.arguments).to.include({
					name: 'a',
					type: 'Integer'
				});
			});

			it('should error if argument object does not have a name', function () {
				expect(obj.addArgument.bind(obj, { type: 'Integer' })).to.throw(Error);
			});

			it('should error if argument object does not have a type', function () {
				expect(obj.addArgument.bind(obj, { name: 'a' })).to.throw(Error);
			});

			it('should error if argument name already exists in that method', function () {
				obj.addArgument({
					name: 'a',
					type: 'Integer'
				});

				// Validate the argument now exists.
				expect(obj.arguments).to.include({
					name: 'a',
					type: 'Integer'
				});

				expect(obj.addArgument.bind(obj, {
					name: 'a',
					type: 'Integer'
				})).to.throw(Error);
			});
		});

		describe('#addPrecondition', function () {
			let obj;

			beforeEach(function () {
				obj = new TestClass('foo', 'Integer');
			});

			it('should error on empty', function () {
				expect(obj.addPrecondition).to.throw(Error);
			});

			it('should error if argument is not an object', function () {
				expect(obj.addPrecondition.bind(obj, '(> a b)')).to.throw(Error);
			});

			it('should add a new precondition', function () {
				const preconditionsLength = obj.preconditions.length;

				obj.addPrecondition({
					comparison: 'LessThan',
					arguments: [
						'a',
						'b'
					]
				});

				expect(obj.preconditions.length).to.equal(preconditionsLength + 1);
			});

			it('should generate a unique ID for the condition', function () {
				obj.addPrecondition({
					comparison: 'LessThan',
					arguments: [
						'a',
						'b'
					]
				});

				expect(obj.preconditions[0].id).to.be.a('string').and.match(REGEX_UUID);
			});

			it('should error if precondition object does not specify the comparison', function () {
				expect(obj.addPrecondition.bind(obj, {
					comparison: undefined,
					arguments: [
						'a',
						'b'
					]
				})).to.throw(Error);
			});

			it('should error if precondition object does not specify at least 1 item in arguments', function () {
				expect(obj.addPrecondition.bind(obj, {
					comparison: 'LessThan',
					arguments: []
				})).to.throw(Error);
			});
		});

		describe('#addPostcondition', function () {
			let obj;

			beforeEach(function () {
				obj = new TestClass('foo', 'Integer');
			});

			it('should error on empty', function () {
				expect(obj.addPostcondition).to.throw(Error);
			});

			it('should error if argument is not an object', function () {
				expect(obj.addPostcondition.bind(obj, '(> a b)')).to.throw(Error);
			});

			it('should add a new postcondition', function () {
				const postconditionsLength = Object.keys(obj.postconditions).length;

				obj.addPostcondition({
					comparison: 'LessThan',
					arguments: [
						'a',
						'b'
					]
				});

				expect(Object.keys(obj.postconditions).length).to.equal(postconditionsLength + 1);
			});

			it('should generate a unique ID for the condition', function () {
				obj.addPostcondition({
					comparison: 'LessThan',
					arguments: [
						'a',
						'b'
					]
				});

				expect(obj.postconditions[0].id).to.be.a('string').and.match(REGEX_UUID);
			});

			it('should error if postcondition object does not specify the comparison', function () {
				expect(obj.addPostcondition.bind(obj, {
					comparison: undefined,
					arguments: [
						'a',
						'b'
					]
				})).to.throw(Error);
			});

			it('should error if postcondition object does not specify at least 1 item in arguments', function () {
				expect(obj.addPostcondition.bind(obj, {
					comparison: 'LessThan',
					arguments: []
				})).to.throw(Error);
			});
		});
	});

	describe('OclCondition', function () {
		before(function () {
			TestClass = testee.OclCondition;
		});

		it('should error on empty', function () {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should error if condition is not an object', function () {
			expect(() => {
				new TestClass('(> a b)');
			}).to.throw(Error);
		});

		it('should take a condition object', function () {
			const obj = new TestClass({
				comparison: 'LessThan',
				arguments: [
					'a',
					'b'
				]
			});

			expect(obj.comparison).to.equal('LessThan');
			expect(obj.arguments).to.include('a').and.include('b');
			expect(obj.isInverted).to.not.be.ok;
		});

		it('should error if condition does not have a comparison', function () {
			expect(() => {
				new TestClass({
					comparison: undefined,
					arguments: [
						'a',
						'b'
					]
				});
			}).to.throw(Error);
		});

		it('should error if condition is not an Array', function () {
			expect(() => {
				new TestClass({
					comparison: 'GreaterThan',
					arguments: 'a, b'
				});
			}).to.throw(Error);
		});

		it('should error if condition does not have at least one argument', function () {
			expect(() => {
				new TestClass({
					comparison: 'GreaterThan',
					arguments: []
				});
			}).to.throw(Error);
		});

		it('should set isInverted value in object', function () {
			const obj = new TestClass({
				comparison: 'LessThan',
				arguments: [
					'a',
					'b'
				],
				isInverted: true
			});

			expect(obj.comparison).to.equal('LessThan');
			expect(obj.arguments).to.include('a').and.include('b');
			expect(obj.isInverted).to.be.ok;
		});

		describe('#setInverted', function () {
			let obj;

			beforeEach(function () {
				obj = new TestClass({
					comparison: 'LessThan',
					arguments: [
						'a',
						'b'
					]
				});
			});

			it('should error on empty input', function () {
				expect(obj.setInverted).to.throw(Error);
			});

			it('should error if value is not a boolean', function () {
				expect(obj.setInverted.bind(obj, 'true')).to.throw(Error);
			});

			it('should set isInverted flag to value', function () {
				// Validate change occurs due to method call.
				expect(obj.isInverted).to.be.not.ok;

				obj.setInverted(true);

				expect(obj.isInverted).to.be.ok;
			});
		});

		describe('#setException', function () {
			let obj;

			beforeEach(function () {
				obj = new TestClass({
					comparison: 'LessThan',
					arguments: [
						'a',
						'b'
					]
				});
			});

			it('should error on empty', function () {
				expect(obj.setException).to.throw(Error);
			});

			it('should take type name for an Exception', function () {
				expect(obj.exception).to.be.undefined;

				obj.setException('NullException');

				expect(obj.exception).to.include({ type: 'NullException' });
			});
		});
	});
});
