import React, { useState, useRef, ChangeEvent } from 'react';
import { makeStyles } from '@material-ui/core/styles';
import Typography from '@material-ui/core/Typography';
import Popover from '@material-ui/core/Popover';
import TextField from '@material-ui/core/TextField';
import SearchIcon from '@material-ui/icons/Search';
import Divider from '@material-ui/core/Divider';
import InputAdornment from '@material-ui/core/InputAdornment';
import useDebounce from '../useDebounce';
import List from '../ListWIthId';
import ClickAwayListener from '@material-ui/core/ClickAwayListener';
import { DEFAULT_SCROLL_DIV_HEIGHT, DEFAULT_ITEM_HEIGHT } from '../const';
import MultipleSectionItem, { ChoiceSections, Choice } from './MultipleSectionItem';

const useStyles = makeStyles({
  popOver: {
    '& .MuiPaper-root': {
      zIndex: 1400,
      alignItems: 'center',
      borderRadius: 0,
      display: 'flex',
      flexDirection: 'column',
      justifyContent: 'center',
      boxShadow: 'none',
      background: 'transparent',
      padding: '0 20px',
    },
  },
  popUp: (props: { selectDivWidth: number }) => ({
    zIndex: 1410,
    width: props.selectDivWidth,
    backgroundColor: 'white',
    height: 'fit-content',
    display: 'flex',
    flexFlow: 'wrap column',
    overflow: 'visible',
    borderRadius: 4,
    boxShadow:
        '0 4px 8px 0 rgba(0, 0, 0, 0.2), 0 6px 20px 0 rgba(0, 0, 0, 0.19)',
  }),
  searchDiv: {
    '& .MuiInput-input': {
      padding: '10px 15px',
    },
  },
  input: {
    '&::placeholder': {
      fontStyle: 'italic',
    },
  },
  sectionName: {
    display: 'flex',
    alignItems: 'center',
    textAlign: 'left',
    height: '100%',
    padding: '0px 16px',
    backgroundColor: '#F7F7F7',
    borderTop: '1px solid #F3F3F3',
    borderBottom: '1px solid #F3F3F3',
  },
  clearAll: {
    marginTop: 5,
    position: 'relative',
    minWidth: 'fit-content',
    display: 'flex',
    alignItems: 'center',
    flexDirection: 'row',
    backgroundColor: 'black',
    opacity: 0.8,
    borderRadius: 4,
    padding: '10px 15px',
    '& *': {
      color: 'white',
      userSelect: 'none',
    },
  },
  divider: {
    margin: '0 15px',
    height: '20px',
    background: 'white',
    width: '1px',
  },
  clearAllButtom: {
    cursor: 'pointer',
  },
});

export interface Props {
  name: string;
  chosenChoice: {[key:string]: Choice | null};
  popUpKey: string;
  anchorEl: HTMLDivElement;
  choiceSections: ChoiceSections[];
  id?: string;
  itemHeight?: number;
  scrollDivHeight?: number;
  handleClose: (chosenChoice: {[key:string]: Choice | null}) => void;
  handleSelect: (value: Choice, isCheck: boolean) => void;
  handleClearAll: () => void;
}

const MultipleSelectorPopup: React.FC<Props> = ({
  name,
  chosenChoice,
  popUpKey,
  anchorEl,
  choiceSections,
  id,
  itemHeight = DEFAULT_ITEM_HEIGHT,
  scrollDivHeight = DEFAULT_SCROLL_DIV_HEIGHT,
  handleClose,
  handleSelect,
  handleClearAll,
}) => {
  const popupRef = useRef<HTMLDivElement>(null);
  const [searchWord, setSearchWord] = useState<string>('');
  const debouncedSearchWord = useDebounce(searchWord, 100);
  const classes = useStyles({ selectDivWidth: anchorEl?.clientWidth });

  const handleSeaching = (e: ChangeEvent<HTMLTextAreaElement | HTMLInputElement>) => {
    setSearchWord(e.target.value);
  };

  const selectedChoicesLength = Object.values(chosenChoice)
    .filter((value) => Boolean(value))
    .length;

  const filterChoices = (section: ChoiceSections, searchString: string) => {
    const sectionChoices = section.choices.reduce((acc, choice) => {
      if (new RegExp(`${searchString.replace(/\[|\]|\(|\)|\+|-|\*|\\|\?|\^|\$/g, (e) => (`\\${e}`))}`, 'i').test(choice.label)) {
        return [...acc, { ...choice, sectionPrefix: section.sectionPrefix }];
      }
      return acc;
    }, []);
    if (sectionChoices.length > 0) {
      return [...section.sectionName ? [`${section.sectionName} (${sectionChoices.length})`] : [], ...sectionChoices];
    }
    return null;
  };

  const choices = choiceSections
    .reduce((acc, section: ChoiceSections) => {
      const filteredSection = filterChoices(section, debouncedSearchWord);
      return filteredSection ? [...acc, ...filteredSection] : acc;
    }, []);

  const listHeight = (choices.length * itemHeight) > scrollDivHeight
    ? scrollDivHeight : choices.length * itemHeight;

  return (
    <Popover
      key={`popper-${popUpKey}`}
      open
      anchorEl={anchorEl}
      anchorOrigin={{
        vertical: 'bottom',
        horizontal: 'center',
      }}
      transformOrigin={{
        vertical: 'top',
        horizontal: 'center',
      }}
      className={classes.popOver}
      ref={popupRef}
    >
      <ClickAwayListener onClickAway={() => { handleClose(chosenChoice); }}>
        <div className={classes.popUp}>
          <TextField
            fullWidth
            placeholder="Search"
            className={classes.searchDiv}
            InputProps={{
              disableUnderline: true,
              classes: { input: classes.input },
              endAdornment: <InputAdornment position="start"><SearchIcon style={{ fontSize: '18px' }} /></InputAdornment>,
            }}
            onChange={handleSeaching}
            id={`${id}-seach-textfield`}
            autoComplete="off"
          />
          <List
            height={listHeight}
            itemCount={choices.length}
            itemSize={itemHeight}
            width={anchorEl?.clientWidth}
            overscanCount={10}
            outerId={`${id}-list-outer-div`}
            innerId={`${id}-list-inner-div`}
          >
            {({ index, style }) => {
              const choice = choices[index];
              return (
              <div id={`${id}-${index}-choice-div`} style={{ ...style, height: itemHeight }}>
                {(typeof choice === 'string')
                  ? <Typography className={classes.sectionName}>{choice}</Typography>
                  : (
                    <MultipleSectionItem
                      key={`item-${index + 1}`}
                      choice={choice}
                      checked={Boolean(chosenChoice[`${choice.singleChoice ? 'Single -' : ''}${choice?.isGroup ? 'Group -' : ''}${choice?.id ?? choice.label}`])}
                      handleSelect={handleSelect}
                      id={id}
                    />
                  )}
              </div>
            )}}
          </List>
        </div>
      </ClickAwayListener>
      <div className={classes.clearAll} style={{ opacity: selectedChoicesLength > 1 ? 1 : 0 }}>
        <Typography>{`${selectedChoicesLength} ${name}s are selected`}</Typography>
        <Divider orientation="vertical" classes={{ root: classes.divider }} flexItem />
        <Typography onClick={handleClearAll} id={`${id}-clear-button`} className={classes.clearAllButtom}>Clear All</Typography>
      </div>
    </Popover>
  );
};

export default MultipleSelectorPopup;
