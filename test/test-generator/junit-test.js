const path = require('path');
const yeomanHelpers = require('yeoman-test');

const promises = require('../../util/promises.js');

describe('JUnit', function () {
	let generatedTestSuite;

	before(function () {
		const fixture = require(global.fixtures.FullModels.SimpleMath['input-generator']);

		return yeomanHelpers.run(path.join(__dirname, '../../generators/app'))
			.inDir('test/tmp/junit/')
			.withOptions({
				model: JSON.stringify(fixture),
				framework: 'junit'
			}).then(() => {
				return promises.fsReadFile('build/SimpleMathTest.java');
			}).then((data) => {
				generatedTestSuite = data;
			});
	});

	it('should make a test suite for SimpleMath', function () {
		expect(generatedTestSuite).to.exist;
	});

	it('should have a test setUp', function () {
		expect(generatedTestSuite).to.have.string('@Before');
		expect(generatedTestSuite).to.have.string('void setUp');
		expect(generatedTestSuite).to.have.string('SimpleMath testee');
		expect(generatedTestSuite).to.have.string('testee = new SimpleMath()');
	});

	it('should have 3 tests for Add', function () {
		const match = generatedTestSuite.match(/test_Add/g);

		expect(match).to.have.length(3);
	});

	it('should have 3 tests for Subtract', function () {
		const match = generatedTestSuite.match(/test_Subtract/g);

		expect(match).to.have.length(3);
	});

	it('should have 3 tests for Divide', function () {
		const match = generatedTestSuite.match(/test_Divide/g);

		expect(match).to.have.length(3);
	});

	it('should have 2 tests for SquareRoot', function () {
		const match = generatedTestSuite.match(/test_SquareRoot/g);

		expect(match).to.have.length(2);
	});

	it('should have converted "Integer" to "int"', function () {
		expect(generatedTestSuite).to.match(/int/);
		expect(generatedTestSuite).to.not.match(/Integer/);
	});

	after(function () {
		// Reset location due to changing from helpers running in specific directory.
		process.chdir('../../../');
	});
});
