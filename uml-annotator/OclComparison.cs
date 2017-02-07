using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace UmlAnnotator
{
	public class OclComparison
	{
		string name;
		public string Name
		{
			get { return name; }
		}

		string symbol;
		string smtSymbol;
		bool invertable;

		public OclComparison(string name, string symbol, string smtSymbol, bool? invertable)
		{
			this.name = name;
			this.symbol = symbol;

			if (!String.IsNullOrEmpty(smtSymbol))
			{
				this.smtSymbol = smtSymbol;
			}
			else
			{
				this.smtSymbol = symbol;
			}

			this.invertable = invertable == true;
		}

		public string SymbolString()
		{
			return smtSymbol;
		}

		public override string ToString()
		{
			return String.Format("{0} ({1})", symbol, name);
		}
	}
}
